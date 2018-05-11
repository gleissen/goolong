package main

import (
	"flag"
	"fmt"
	"gochai"
)

var myID = flag.Int("id", 0, "Replica id")
var myAddr = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")

func main() {
	flag.Parse()
	peerAddresses := flag.Args()
	fmt.Printf("Peer addresses: %v\n", peerAddresses)
	doneFollower := make(chan bool, 1)
	doneCandidate := make(chan bool, 1)
	go runFollower(peerAddresses, doneFollower)
	go runCandidate(peerAddresses, doneCandidate)
	// wait for follower and candidate to finish
	fmt.Printf("main: waiting for follower.\n")
	<-doneFollower
	fmt.Printf("main: waiting for candidate.\n")
	<-doneCandidate
	fmt.Printf("done.\n")
}

func runCandidate(peerAddresses []string, done chan bool) {
	n := gochai.CreateNewNode("c", *myID, *myAddr, peerAddresses, true)
	// Declaring protocol state
	term := gochai.NewVar()
	id := gochai.NewVar()
	vote := gochai.NewVar()
	count := gochai.NewVar()
	leader := gochai.NewVar()
	id.Assign(int32(*myID))
	// Initializations
	leader.Assign(0)
	count.Assign(0)
	fmt.Printf("Candidate: please enter term number:\n")
	term.ReadIO()
	// part of symmetric set "cs"
	n.StartSymSet("cs", "c")
	// -- begin protocol
	for Peer := range n.PeerIds {
		// {-@ invariant: true -@}
		// send proposal to follower
		msg := gochai.MakePair(id, term)
		fmt.Printf("Candidate: sending request for id %v and term %v to %v:\n", id.Get(), term.Get(), Peer)
		n.Send(Peer, msg)
		vote = n.RecvFrom(Peer)
		fmt.Printf("Candidate: received vote: %v\n", vote.Get())
		if vote.Get() == 1 {
			count.Assign(count.Get() + 1)
		}
	}
	if 2*int(count.Get()) > n.N {
		leader.Assign(1)
	}
	fmt.Printf("received %v votes\n", leader.Get())
	if leader.Get() == 1 {
		fmt.Printf("I'm the leader!!")
	} else {
		fmt.Printf("Not the leader.")
	}
	// --end
	fmt.Printf("candidate: done.. shutting down.\n")
	n.Shutdown()
	done <- true
}

func runFollower(peerAddresses []string, done chan bool) {
	n := gochai.CreateNewNode("f", *myID, *myAddr, peerAddresses, false)
	// Initializations
	myTerm := gochai.NewVar()
	voted := gochai.NewVar()
	votedFor := gochai.NewVar()
	myVote := gochai.NewVar()
	votes := gochai.NewMap()
	myTerm.Assign(-1)
	voted.Assign(0)
	n.AssignSymSet("fs", "")
	// -- begin protocol
	for i := range n.PeerIds {
		// {-@ invariant: true -@}
		myVote.Assign(0)
		id, t := n.RecvPair()
		fmt.Printf("follower: received request for id %v and term %v \n", id.Get(), t.Get())
		// proceed if the request is not outdated
		if t.Get() > myTerm.Get() {
			myTerm.Assign(t.Get())
			voted.Assign(0)
			votedFor.Assign(0)
		}
		if t.Get() >= myTerm.Get() && (voted.Get() == 0 || votedFor.Get() == id.Get()) {
			voted.Assign(1)
			votedFor.Assign(id.Get())
			votes.Put(myTerm.Get(), id.Get())
			myVote.Assign(1)
		}
		fmt.Printf("follower: round %v, casting vote %v for %v\n", i, myVote.Get(), id.Get())
		n.Send(int(id.Get()), myVote)
	}
	fmt.Printf("follower: done.. shutting down.\n")
	n.Shutdown()
	done <- true
	//--end
}

// {-@ ensures: and([forall([decl(i,int)], implies(and([elem(i,dbs), committed=1]), ref(value,i)=proposal)), forall([decl(i,int)], implies(and([elem(i,dbs), committed=0]), ref(value,i)=0))]) -@}
