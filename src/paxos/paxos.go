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
	myTerm := gochai.NewVar()
	id := gochai.NewUInt8()
	xT := gochai.NewVar() // highest term variable seen so far
	x := gochai.NewVar()  // proposal value
	ho := gochai.NewVar()
	ready := gochai.NewVar()
	decided := gochai.NewVar()

	// Initializations
	myTerm.Assign(int32(*termArg))
	xT.Assign(0)
	x.Assign(int32(*proposalArg))
	ho.Assign(0)
	ready.Assign(0)
	decided.Assign(0)

	// =====================
	//    Sending Proposals
	// =====================
	for Peer := range n.PeerIds {

		id.Assign(uint8(n.MyId()))
		// propose myTerm
		fmt.Printf("prop: sending proposal %v and id %v to %v\n", myTerm.Get(), id.Get(), Peer)
		n.SendPrepare(Peer, id, myTerm)
		// receive highest accepted term w_t and accepted value w
		rwT, rw, rsuccess := n.RecvAcceptorReplyFrom(Peer)
		fmt.Printf("prop: received answer rwT:%v and rw:%v from %v\n", rwT.Get(), rw.Get(), Peer)
		// if not outdated
		if rsuccess.Get() == 1 {
			ho.Assign(ho.Get() + 1)
		}
		// if a newer value was accepted, propose that value instead
		if rwT.Get() >= xT.Get() {
			xT.Assign(rwT.Get())
			x.Assign(rw.Get())
		}
	}
	if 2*int(ho.Get()) > n.NumPeers() {
		fmt.Printf("\n\nprop: entering acceptance phase!\n\n")
		// =====================
		//    Sending Accepts
		// =====================
		ho.Assign(0)
		ready.Assign(1)

		for Peer := range n.PeerIds {
			fmt.Printf("prop: sending accept for value %v and ballot %v to %v.\n", myTerm.Get(), x.Get(), Peer)
			n.SendAccept(Peer, id, myTerm, x)
			_, _, rsuccess := n.RecvAcceptorReplyFrom(Peer)
			fmt.Printf("prop: received reply %v from %v .\n", rsuccess.Get(), Peer)
			if rsuccess.Get() == 1 {
				ho.Assign(ho.Get() + 1)
			}
		}
		if 2*int(ho.Get()) > n.NumPeers() {
			decided.Assign(1)
			fmt.Printf("prop: value %v for ballot %v accepted, yay!\n", x.Get(), myTerm.Get())
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
		msgType, resID, t, x := n.AcceptorReceive()
		switch msgType.Get() {

		// prepare message
		case PrepareType:
			fmt.Printf("acc: received proposal %v from %v\n", t.Get(), resID.Get())
			success.Assign(0)
			if t.Get() > max.Get() {
				max.Assign(t.Get())
				success.Assign(1)
			}

			// accept message
		case AcceptType:
			fmt.Printf("acc: received accept of %v with ballot %v from %v\n", x.Get(), t.Get(), resID.Get())
			success.Assign(0)
			if t.Get() >= max.Get() {
				wT.Assign(t.Get())
				w.Assign(x.Get())
				success.Assign(1)
				fmt.Printf("acc: accepted value %v for ballot %v \n", w.Get(), wT.Get())

			}
		}
		// Sending reply
		fmt.Printf("acc: sending reply: wt:%v, w:%v, success:%v to %v \n", wT.Get(), w.Get(), success.Get(), resID.Get())
		n.SendAcceptorReply(int(resID.Get()), wT, w, success)
	}
}

/*{-@ ensures: forall([decl(i,int), decl(j,int)],
			implies(
					and([
						elem(i,cs),
						elem(j,cs),
						ref(term,i)=ref(term,j),
						ref(isLeader,j)=1,
						ref(isLeader,i)=1
						]),
					i=j
				)
		)
-@}*/
