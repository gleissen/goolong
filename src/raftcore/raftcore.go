package main

import (
	"flag"
	"fmt"
	"gochai"
)

var term = flag.Int("term", 0, "Current term")
var myID = flag.Int("id", 0, "Replica id")
var myAddr = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")

func main() {
	flag.Parse()
	peerAddresses := flag.Args()
	doneFollower := make(chan bool, 1)
	doneCandidate := make(chan bool, 1)
	go runFollower(peerAddresses, doneFollower)
	go runCandidate(peerAddresses, term, doneCandidate)
	// wait for follower and candidate to finish
	<-doneFollower
	<-doneCandidate
	//fmt.Printf("done.\n")
}

func runCandidate(peerAddresses []string, termArg *int, done chan bool) {
	n := gochai.CreateNewNode("c", *myID, *myAddr, peerAddresses, true)
	// Declaring protocol state
	term := gochai.NewVar()
	id := gochai.NewVar()
	vote := gochai.NewVar()
	count := gochai.NewVar()
	leader := gochai.NewVar()
	id.Assign(n.MyId())
	// Initializations
	leader.Assign(0)
	count.Assign(0)
	term.Assign(int32(*termArg))
	// part of symmetric set "cs"
	n.StartSymSet("cs", "c")
	// -- begin protocol
	for Peer := range n.PeerIds {
		// {-@ invariant: true -@}
		// send proposal to follower
		n.SendPair(Peer, id, term)
		vote = n.RecvFrom(Peer)
		if vote.Get() == 1 {
			count.Assign(count.Get() + 1)
		}
	}
	if 2*int(count.Get()) > n.NumPeers() {
		leader.Assign(1)
	}
	if leader.Get() == 1 {
		fmt.Printf("I'm the leader for term %v!!", term.Get())
	} else {
		fmt.Printf("Not the leader in term %v.", term.Get())
	}
	// --end
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
	n.StartSymSet("fs", "f")
	// -- begin protocol
	for _ = range n.PeerIds {
		// {-@ invariant: true -@}
		myVote.Assign(0)
		resID, t := n.RecvPair()
		// proceed if the request is not outdated
		if t.Get() > myTerm.Get() {
			myTerm.Assign(t.Get())
			voted.Assign(0)
			votedFor.Assign(0)
		}
		if t.Get() >= myTerm.Get() && (voted.Get() == 0 || votedFor.Get() == resID.Get()) {
			voted.Assign(1)
			votedFor.Assign(resID.Get())
			//assign(F, votes, upd(votes, myTerm, resId))
			votes.Put(myTerm.Get(), resID.Get())
			myVote.Assign(1)
		}
		n.Send(int(resID.Get()), myVote)
	}
	n.Shutdown()
	done <- true
	//--end
}

// {-@ ensures: and([forall([decl(i,int)], implies(and([elem(i,dbs), committed=1]), ref(value,i)=proposal)), forall([decl(i,int)], implies(and([elem(i,dbs), committed=0]), ref(value,i)=0))]) -@}
