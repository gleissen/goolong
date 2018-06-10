package main

import (
	"flag"
	"fmt"
	"gochai"
)

var term = flag.Int("term", 0, "Current term")
var proposal = flag.Int("proposal", 0, "Proposed value")
var myID = flag.Int("id", 0, "Replica id")
var myAddr = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")

func main() {
	flag.Parse()
	peerAddresses := flag.Args()
	doneFollower := make(chan bool, 1)
	doneCandidate := make(chan bool, 1)
	go runProposer(peerAddresses, term, proposal, doneFollower)
	go runAcceptor(peerAddresses, doneCandidate)
	// wait for follower and candidate to finish
	<-doneFollower
	<-doneCandidate
}

func runProposer(peerAddresses []string, termArg *int, proposalArg *int, done chan bool) {
	n := gochai.CreateNewNode("p", *myID, *myAddr, peerAddresses, false)
	n.StartSymSet("ps", "p")
	n.AssignSymSet("as", "")

	// Declarations
	myTerm := gochai.NewVar()
	id := gochai.NewVar()
	xT := gochai.NewVar() // highest term variable seen so far
	x := gochai.NewVar()  // proposal value
	ho := gochai.NewVar()
	ready := gochai.NewVar()

	// Initializations
	myTerm.Assign(int32(*termArg))
	xT.Assign(0)
	x.Assign(int32(*proposalArg))
	ho.Assign(0)
	ready.Assign(0)

	// =====================
	//    Sending Proposals
	// =====================
	for Peer := range n.PeerIds {

		id.Assign(n.MyId())
		// propose myTerm
		fmt.Printf("prop: sending proposal %v to %v\n", myTerm.Get(), Peer)
		n.SendPair(Peer, id, myTerm)
		// receive highest accepted term w_t and accepted value w
		rmax, rwT := n.RecvPairFrom(Peer)
		fmt.Printf("prop: received answer %v from %v\n", rwT.Get(), Peer)
		// if not outdated
		if myTerm.Get() >= rmax.Get() {
			ho.Assign(ho.Get() + 1)
		}
		// if a newer value was accepted, propose that value instead
		if rwT.Get() >= xT.Get() {
			xT.Assign(rwT.Get())
			//x.Assign(rw.Get())
		}
	}
	if 2*int(ho.Get()) > n.NumPeers() {
		ho.Assign(0)
		ready.Assign(1)
		fmt.Printf("ready to propose value %v...\n", x)
	} else {
		fmt.Printf("nothing to propose...\n")
	}

	// =====================
	//    Sending Accepts
	// =====================

	n.Shutdown()
	done <- true
	//--end
}

func runAcceptor(peerAddresses []string, done chan bool) {
	n := gochai.CreateNewNode("c", *myID, *myAddr, peerAddresses, true)

	// -- Assigning sets --
	n.StartSymSet("as", "a")
	n.AssignSymSet("ps", "")

	// Declarations
	max := gochai.NewVar()
	wT := gochai.NewVar()
	w := gochai.NewVar()

	// Initializations
	max.Assign(-1)
	wT.Assign(-1)
	w.Assign(-1)
	for _ = range n.PeerIds {
		resID, t := n.RecvPair()
		fmt.Printf("acc: received proposal %v from %v\n", t.Get(), resID.Get())
		if t.Get() > max.Get() {
			max.Assign(t.Get())
		}
		fmt.Printf("acc: sending reply\n")
		n.SendPair(int(resID.Get()), max, wT)
	}
	n.Shutdown()
	done <- true
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
