package main

import (
	"fmt"
	"flag"
	"gochai"
)

var term = flag.Int("term", 0, "Current term")
var myID = flag.Int("id", 0, "Replica id")
var myAddr = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")

func main() {
	flag.Parse()
	peerAddresses := flag.Args()
	donePs := make(chan bool, 1)
	doneQs := make(chan bool, 1)
	go runPs(peerAddresses, donePs)
	go runQs(peerAddresses, doneQs)
	// wait for follower and candidate to finish
	<-donePs
	<-doneQs
}

func runPs(peerAddresses []string, done chan bool) {
	n := gochai.CreateNewNode("p", *myID, *myAddr, peerAddresses, false)
	n.Start()
	n.StartSymSet("ps", "p")
	n.AssignSymSet("qs", "")

	pv := gochai.NewVar()
	pv.Assign(1)

	pid := gochai.NewVar()
	pid.Assign(n.MyId())

	px := gochai.NewVar()
	for Q := range n.PeerIds {
		/*{-@ invariant: forall([decl(i,int)],
								implies(elem(i,rr), ref(y,i)=1))
		-@}*/
		n.SendPair(Q, pid, pv)
	}

	for _ = range n.PeerIds {
		px = n.Recv()
	}

	fmt.Printf("px:%v\n", px.Get())

	n.Shutdown()
	done <- true
}

func runQs(peerAddresses []string, done chan bool) {
	n := gochai.CreateNewNode("c", *myID, *myAddr, peerAddresses, true)
	n.Start()

	n.StartSymSet("qs", "q")
	n.AssignSymSet("ps", "")

	qid := gochai.NewVar()
	y := gochai.NewVar()

	for _ = range n.PeerIds {
		qid, y := n.RecvPair()
		n.Send(int(qid.Get()), y)
	}

	fmt.Printf("qid:%v, y:%v\n", qid.Get(), y.Get())

	n.Shutdown()
	done <- true
}

/*{-@ ensures: 
	  forall([decl(i,int)], implies(elem(i,qs), ref(y,i)=1))
-@}*/
