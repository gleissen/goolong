package main

import (
	"flag"
	"fmt"
	"gochai"
	"log"
	"os"
	"os/signal"
	"paxosproto"
)

// =============
//  Main entry
// =============

const (
	PrepareType uint8 = 0
	AcceptType        = 1
)

var term = flag.Int("term", 0, "Current term")
var proposal = flag.Int("proposal", 0, "Proposed value")
var myID = flag.Int("id", 0, "Replica id")
var myAddr = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")

func main() {
	flag.Parse()
	peerAddresses := flag.Args()
	if *myID < 0 || *myID >= len(peerAddresses) {
		log.Fatal("id: index out of bounds")
	}
	if *term < 1 {
		log.Fatal("term: pick a term>0.")
	}

	doneProposer := make(chan bool, 1)
	doneAcceptor := make(chan bool, 1)
	interrupt := make(chan os.Signal, 1)
	signal.Notify(interrupt)
	go catchKill(interrupt, doneAcceptor)
	go runProposer(peerAddresses, term, proposal, doneProposer)
	go runAcceptor(peerAddresses)
	<-doneProposer
	fmt.Printf("\n\nmain: proposer finished!\n\n")
	<-doneAcceptor
}

func catchKill(interrupt chan os.Signal, done chan bool) {
	<-interrupt
	fmt.Println("Caught signal; exiting")
	done <- true
}

// ==========
//  Proposer
// ==========

func runProposer(peerAddresses []string, termArg *int, proposalArg *int, done chan bool) {
	n := paxosproto.NewPaxosNode("p", *myID, *myAddr, peerAddresses, false)
	n.Start()
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
	// Ghost variables
	k := gochai.NewVar() // k = #{a ∈ as | p.t ∈ a.ts}
	l := gochai.NewVar() // l = #{a ∈ as | p.t ∉ a.ts ∧ a.max ≤ p.t}
	m := gochai.NewVar() // m = #{a ∈ as | p.t ∉ a.ts ∧ a.max > p.t}
	// just to stop it from complaining..
	fmt.Printf("%v%v%v", k, l, m)

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
	t.Assign(int32(*termArg))
	xT.Assign(0)
	x.Assign(int32(*proposalArg))
	ho.Assign(0)
	ready.Assign(0)
	decided.Assign(0)
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
		fmt.Printf("prop: sending proposal %v and id %v to %v\n", t.Get(), id.Get(), Peer)
		n.SendPrepare(Peer, id, t)
		// receive highest accepted term w_t and accepted value w

		//{-@ group: start -@}
		rwT, rw, rsuccess := n.RecvAcceptorReplyFrom(Peer)
		fmt.Printf("prop: received answer rwT:%v and rw:%v from %v with %v \n", rwT.Get(), rw.Get(), Peer, rsuccess.Get())
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
		fmt.Printf("\n\nprop: entering acceptance phase!\n\n")

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
			/*{-@pre: ducko -@}*/

			n.SendAccept(Peer, id, t, x)

			fmt.Printf("prop: sending accept for value %v and ballot %v to %v.\n", t.Get(), x.Get(), Peer)
			rwT, rw, rsuccess := n.RecvAcceptorReplyFrom(Peer)
			fmt.Printf("prop: received reply %v from %v (also %v and %v).\n", rsuccess.Get(), Peer, rwT.Get(), rw.Get())
			if rsuccess.Get() == 1 {
				ho.Assign(ho.Get() + 1)
				// ghost updates
				k.Assign(k.Get() + 1)
				l.Assign(l.Get() - 1)
			}
		}
		if 2*int(ho.Get()) > n.NumPeers() {
			decided.Assign(1)
			fmt.Printf("prop: value %v for ballot %v accepted, yay!\n", x.Get(), t.Get())
		}
	} else {
		fmt.Printf("prop: proposal failed.\n")
	}
	n.Shutdown()
	done <- true
	//--end
}

// ============
//   Acceptor
// ============

func runAcceptor(peerAddresses []string) {
	n := paxosproto.NewPaxosNode("c", *myID, *myAddr, peerAddresses, true)
	n.Start()
	// -- Assigning sets --
	n.StartSymSet("as", "a")
	n.AssignSymSet("ps", "")

	// Declarations
	max := gochai.NewVar()
	wT := gochai.NewVar()
	w := gochai.NewVar()
	success := gochai.NewUInt8()
	// Initializations
	max.Assign(-1)
	wT.Assign(-1)
	w.Assign(-1)
	for {
		// receive request
		msgType, pID, pt, px := n.AcceptorReceive()

		switch msgType.Get() {

		// prepare message
		case PrepareType:
			fmt.Printf("acc: received proposal %v from %v\n", pt.Get(), pID.Get())
			success.Assign(0)
			if pt.Get() > max.Get() {
				max.Assign(pt.Get())
				success.Assign(1)
			}

			// accept message
		case AcceptType:
			fmt.Printf("acc: received accept of %v with ballot %v from %v\n", px.Get(), pt.Get(), pID.Get())
			success.Assign(0)
			if pt.Get() >= max.Get() {
				wT.Assign(pt.Get())
				w.Assign(px.Get())
				success.Assign(1)
				fmt.Printf("acc: accepted value %v for ballot %v \n", w.Get(), wT.Get())
			}
		}
		// Sending reply
		fmt.Printf("acc: sending reply: wt:%v, w:%v, success:%v to %v \n", wT.Get(), w.Get(), success.Get(), pID.Get())
		n.SendAcceptorReply(int(pID.Get()), wT, w, success)
	}
}

/*{-@ ensures: true -@}*/
