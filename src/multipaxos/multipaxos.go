package main

import (
	"clientproto"
	"dlog"
	"flag"
	"fmt"
	"gochai"
	"log"
	"multiproto"
	"os"
	"os/signal"
	"state"
	"sync"
	"time"
)

// =============
//  Protocol
// =============

const (
	PrepareType uint8 = 0
	AcceptType        = 1
)
const INSTANCE_SIZE = 20000
const MAX_BATCH = 5000

var myID = flag.Int("id", 0, "Replica id. Defaults to 0.")
var myAddr = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")
var batching = flag.Bool("b", false, "Batching Proposals. Defaults to false.")

var propNode *multiproto.MultiNode
var doneProp = make(chan bool, 1)
var logMutex = &sync.Mutex{}

type InstanceStatus int

const (
	PREPARED InstanceStatus = iota
	ACCEPTED
	COMMITTED
)

type Instance struct {
	Commands []state.Command
	Status   InstanceStatus
}

var Log []*Instance = make([]*Instance, INSTANCE_SIZE) // log of all executed commands

func catchKill(interrupt chan os.Signal, nodes []*multiproto.MultiNode) {
	<-interrupt
	fmt.Println("Caught signal; exiting")
	for _, n := range nodes {
		n.Shutdown()
	}
}

func main() {
	flag.Parse()
	peerAddresses := flag.Args()
	if *myID < 0 || *myID >= len(peerAddresses) {
		log.Fatal("id: index out of bounds")
	}

	propNode := multiproto.NewMultiNode("p", *myID, *myAddr, peerAddresses, false)
	go propNode.Run()
	accNode := multiproto.NewMultiNode("c", *myID, *myAddr, peerAddresses, true)
	go accNode.Run()
	go applyCommits(accNode)
	go executeCommands(accNode)
	interrupt := make(chan os.Signal, 1)
	signal.Notify(interrupt)
	go catchKill(interrupt, []*multiproto.MultiNode{propNode, accNode})

	go runAcceptor(peerAddresses, accNode)

	for !propNode.Stop {
		proposal := <-propNode.ProposeChan
		/*
			if *batching {
				batchSize := len(propNode.ProposeChan) + 1
				if batchSize > MAX_BATCH {
					batchSize = MAX_BATCH
				}
				dlog.Printf("Batched %d\n", batchSize)
				cmds := make([]state.Command, batchSize)
				proposals := make([]*multiproto.Propose, batchSize)
				cmds[0] = proposal.Command
				proposals[0] = proposal
			} */

		dlog.Printf("Proposal with op %d for intance %v\n", proposal.Command.Op, propNode.CrtInstance)
		var ok uint8 = 0
		ballot := propNode.MakeUniqueBallot(1)
		decided := runProposer(propNode, ballot, proposal, propNode.CrtInstance)
		if decided {
			ok = 1
		}
		go propNode.ReplyPropose(&clientproto.ProposeReply{OK: ok, CommandId: proposal.CommandId}, proposal.Wire)
		propNode.BroadcastCommit(ballot, propNode.CrtInstance)
		propNode.CrtInstance++
	}
}

// Commits

func updateCommittedUpTo(n *multiproto.MultiNode) {
	for Log[n.CommittedUpTo+1] != nil &&
		Log[n.CommittedUpTo+1].Status == COMMITTED {
		n.CommittedUpTo++
	}
}

func applyCommits(n *multiproto.MultiNode) {
	for !n.Stop {
		inst, t := n.RecvCommit()
		logMutex.Lock()
		dlog.Printf("Committed instance %v for ballot %v", inst, t)
		Log[inst].Status = COMMITTED
		updateCommittedUpTo(n)
		logMutex.Unlock()
	}
}

func executeCommands(n *multiproto.MultiNode) {
	i := int32(0)
	for !n.Stop {
		executed := false
		for i <= n.CommittedUpTo {
			for _, cmd := range Log[i].Commands {
				dlog.Printf("Executing command %v for key:%v and value:%v", cmd.Op, cmd.K, cmd.V)
				cmd.Execute(n.State)
			}
			i++
			executed = true
		}
		if !executed {
			time.Sleep(1000 * 1000)
		}
	}
}

// ==========
//  Proposer
// ==========

func runProposer(n *multiproto.MultiNode, ballot int32, proposal *multiproto.Propose, instance int32) bool {
	n.StartSymSet("ps", "p")
	n.AssignSymSet("as", "")

	// Declarations
	t := gochai.NewVar()
	id := gochai.NewUInt8()
	xT := gochai.NewVar() // highest term variable seen so far
	x := gochai.NewVar()  // proposal value
	ho := gochai.NewVar()
	ready := gochai.NewVar()
	decided := gochai.NewVar()
	inst := gochai.NewVar()
	// Ghost variables
	k := gochai.NewGhostVar() // k = #{a ∈ as | p.t ∈ a.ts}
	l := gochai.NewGhostVar() // l = #{a ∈ as | p.t ∉ a.ts ∧ a.max ≤ p.t}
	m := gochai.NewGhostVar() // m = #{a ∈ as | p.t ∉ a.ts ∧ a.max > p.t}
	dlog.Printf("%v", m)
	// =====================
	//    Initialization
	// =====================

	/*{-@ pre: and([
					ref(t,P)>0,
					ref(ready,P)=0,
					ref(decided,P)=0,
					ref(ho,P)=0,
					ref(k,P) = 0,
					ref(l,P) = card(as),
					ref(m,P) = 0
				])
	 -@}*/

	t.Assign(ballot)
	xT.Assign(0)
	x.Assign(int32(proposal.CommandId))
	ho.Assign(0)
	ready.Assign(0)
	decided.Assign(0)
	inst.Assign(instance)
	/*{-@ assume: forall([decl(i,int)],
										and([
											ref(t,i) > 0,
											ref(m,i)=0,
											ref(l,i) = card(as),
											ref(k,i) = 0
										])
							)
	-@}*/

	// =====================
	//    Proposal phase
	// =====================

	for Peer := range n.PeerIds {
		// Precondition

		/*{-@pre: forall([decl(i,int)],
						implies(
									and([
												elem(i,ps),
												here(i)
									 		]),
									and([
									 			ref(ready, i)=0,
												ref(decided, i)=0,
												ref(k,i)=0,
												ref(k,i) + ref(l,i) + ref(m,i) = card(as)
											])
										)
									)
		-@}*/
		id.Assign(uint8(n.MyId()))
		// propose myTerm
		dlog.Printf("prop: sending proposal %v for isntance %v to %v\n", t.Get(), inst.Get(), Peer)
		n.SendPrepare(Peer, id, t, inst)
		// receive highest accepted term w_t and accepted value w

		//{-@ group: start -@}
		rwT, rw, rsuccess := n.RecvAcceptorReplyFrom(Peer)
		dlog.Printf("prop: received answer rwT:%v and rw:%v from %v with %v \n", rwT.Get(), rw.Get(), Peer, rsuccess.Get())
		// if not outdated
		if rsuccess.Get() == 1 {
			ho.Assign(ho.Get() + 1)
		}
		// if a newer value was accepted, propose that value instead
		if rwT.Get() >= xT.Get() {
			xT.Assign(rwT.Get())
			x.Assign(rw.Get())
		}
		//{-@ group: end -@}
	}

	if 2*int(ho.Get()) > n.NumPeers() {
		// =====================
		//  Acceptance phase
		// =====================

		/*{-@pre: forall([decl(i,int)],
				implies(
							and([
								elem(i,ps),
								ref(decided,i)=1
							]),
		          and([ ref(k,i) > card(as)/2,
		                ref(ho,i) > card(as)/2,
		                ref(ready,i)=1
		             ])
							)
				)
		-@}*/

		/*{-@pre: forall([decl(i,int)],
							implies(
									and([
										elem(i,ps),
										here(i)
										]),
		             and([
								 		ref(decided,i)=0,
		                ref(k,i)=0,
		                ref(k,i) + ref(l,i) + ref(m,i) = card(as)
		                ])
								)
					)
				-@}*/
		ho.Assign(0)
		ready.Assign(1)

		for Peer := range n.PeerIds {

			/*{-@pre: forall([decl(i,int)],
			              	implies(
														and([
															elem(i,ps),
															here(i)
														]),
			                      and([
															ref(ready,i)=1,
			                        ref(decided,i)=0,
			                        ref(ho,i) =< ref(k,i),
			                        ref(k,i) + ref(l,i) + ref(m,i) = card(as)
			                      ])
											   )
			              )
					-@}*/

			/*{-@pre: forall([decl(i,int), decl(j,int)],
			                          implies(
																	and([
																		elem(i,ps),
																		elem(j,as),
																		ref(l,i) > card(as)/2,
																		ref(k,i)=0
																	]),
			                            ref(wT,j) < ref(t,i)
																)
													)
			-@}*/

			// main invariant
			/*{-@pre: forall([decl(qa,int), decl(qp,int)],
			                          implies(
																	and([
																		elem(qa,as),
																		elem(qp,ps),
																		ref(ready,qp)=1,
																		ref(t,qp) =< ref(wT,qa),
																		ref(k,qp)+ref(l,qp) > card(as)/2
																		]),
			                             ref(w,qa)=ref(x,qp)
																)
													)
			-@}*/

			// Nodes have disjoint tickets

			//{-@ assume: forall([decl(i,int)], implies(ref(t,i)=ref(t,P), i=P)) -@}

			// This fact derived from the cardility invariant over the proposal phase
			/*{-@assume: forall([decl(i,int)],
					implies(
						and([
									elem(i,ps),
									ref(l,i) > card(as)/2
							]),
							or([
									ref(ready,P)=0,
									ref(t,P) < ref(t,i)
								])
							)
				)
			-@}*/

			//{-@declare: decl(a0, int) -@}

			//{-@assume: elem(a0,as) -@}

			/*{-@assume: implies(
											and([0 < ref(xT,P)]),
											and([
														ref(x,P) = ref(w,a0),
														ref(xT,P) = ref(wT,a0)
											])
										)
			-@}*/

			/*{-@assume: forall([decl(i,int)],
														implies(
																and([
																	elem(i,ps),
																	ref(ready,i)=1,
																	ref(k,i)+ref(l,i) > card(as)/2,
																	ref(ready,P)=1
																]),
																and([
																	ref(t,i) =< ref(xT,P),
																	0 < ref(xT,P)
																])
														)
											)
			-@}*/

			n.SendAccept(Peer, id, t, x, inst, proposal)
			dlog.Printf("prop: sending accept for value %v in instance %v with ballot %v to %v.\n", x.Get(), inst.Get(), t.Get(), Peer)

			//{-@ group: start -@}
			rwT, rw, rsuccess := n.RecvAcceptorReplyFrom(Peer)
			dlog.Printf("prop: received reply %v from %v (also %v and %v).\n", rsuccess.Get(), Peer, rwT.Get(), rw.Get())
			if rsuccess.Get() == 1 {
				ho.Assign(ho.Get() + 1)
				// ghost updates
				k.Assign(k.Get() + 1)
				l.Assign(l.Get() - 1)
			}
			//{-@ group: end -@}

		}
		if 2*int(ho.Get()) > n.NumPeers() {

			/*{-@pre: forall([decl(i,int)],
			             implies(
									 		and([elem(i,ps),here(i)]),
			                and([
													ref(ready,i)=1,
			                    ref(ho,i) =< ref(k,i),
			                    ref(k,i) + ref(l,i) + ref(m,i) = card(as)
			                   ])
										)
			          )
			-@}*/
			decided.Assign(1)
			dlog.Printf("prop: value %v for ballot %v accepted.\n", x.Get(), t.Get())
		}
	} else {
		dlog.Printf("prop: proposal failed.\n")
	}
	//--end
	return (decided.Get() == 1)
}

// ============
//   Acceptor
// ============

func runAcceptor(peerAddresses []string, n *multiproto.MultiNode) {

	// -- Assigning sets --
	n.StartSymSet("as", "a")
	n.AssignSymSet("ps", "")

	// Declarations
	max := gochai.NewMap()
	wT := gochai.NewMap()
	w := gochai.NewMap()
	success := gochai.NewUInt8()
	// Initializations

	/*{-@pre: ref(wT,A) = 0 -@}*/
	// assume maps are initialized to 0
	for !n.Stop {
		// receive request
		msgType, pID, inst, pt, px, commands := n.AcceptorReceive()

		switch msgType.Get() {

		// prepare message
		case PrepareType:
			dlog.Printf("acc: received proposal %v from %v for instance %v\n", pt.Get(), pID.Get(), inst.Get())
			success.Assign(0)
			if pt.Get() > max.Get(inst.Get()) {
				max.Put(inst.Get(), pt.Get())
				success.Assign(1)
				logMutex.Lock()
				Log[inst.Get()] = &Instance{commands, PREPARED}
				logMutex.Unlock()
			}

		// accept message
		case AcceptType:
			dlog.Printf("acc: received accept of %v with ballot %v from %v\n", px.Get(), pt.Get(), pID.Get())
			success.Assign(0)
			if pt.Get() >= max.Get(inst.Get()) {
				wT.Put(inst.Get(), pt.Get())
				w.Put(inst.Get(), px.Get())
				success.Assign(1)
				logMutex.Lock()
				Log[inst.Get()] = &Instance{commands, ACCEPTED}
				logMutex.Unlock()
				dlog.Printf("acc: accepted value %v for ballot %v \n", w.Get(inst.Get()), wT.Get(inst.Get()))
			}
		}
		// Sending reply
		dlog.Printf("acc: sending reply: wt:%v, w:%v, success:%v to %v \n", wT.Get(inst.Get()), w.Get(inst.Get()), success.Get(), pID.Get())
		n.SendAcceptorReply(int(pID.Get()), wT.Get(inst.Get()), w.Get(inst.Get()), success.Get())
	}
}

/*{-@ ensures: forall([
									decl(p1,int),
									decl(p2,int)
									],
                  implies(
                      and([
											  elem(a0,as),
                        elem(p1,ps),
                        elem(p2,ps),
                        ref(decided,p1)=1,
                        ref(decided,p2)=1,
                        implies(
														and([
																	ref(k,p1) > card(as)/2,
                                  ref(k,p2) > card(as)/2
															 ]),
                            and([
																	ref(t,p1) =< ref(wT,a0),
																	ref(t,p2) =< ref(wT,a0)
														    ])
													),
                          0 =< ref(l, p1),
													0 =< ref(l ,p2)
											  ]),
                        ref(x,p1) = ref(x,p2))
									)
	-@}*/
