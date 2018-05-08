package main

import (
	"flag"
	"fmt"
	"gochai"
)

const c = 0 // coordinator ID

var isServer = flag.Bool("coord", true, "Act as coordinator (true) or db-node (false). ")
var myID = flag.Int("id", c, "Replica id")
var myAddr = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")

func main() {
	flag.Parse()
	peerAddresses := flag.Args()
	if *isServer {
		runCoordinatorProtocol(peerAddresses)
	} else {
		runServerProtocol(peerAddresses)
	}
}

func runCoordinatorProtocol(peerAddresses []string) {
	n := gochai.CreateNewNode("c", c, *myAddr, peerAddresses, false)
	fmt.Println("Acting as coordinator.")
	n.AssignSymSet("dbs", "")
	proposal := gochai.NewVar()
	decision := gochai.NewVar()
	abort := gochai.NewVar()
	committed := gochai.NewVar()
	committed.Assign(0)
	abort.Assign(0)
	fmt.Println("Please enter your proposal number")
	proposal.ReadIO()
	//Protocol--
	for ID := range n.PeerIds {
		// {-@ invariant: forall([decl(i,int)], implies(and([elem(i,rr)]), and([ref(value,i)=0, ref(val,i)=proposal]))) -@}
		fmt.Printf("Sending proposal to %v\n", ID)
		n.Send(ID, proposal)
		decision = n.Recv()
		fmt.Printf("Received %v\n", decision.Get())
	}
	if decision.Get() == 1 {
		abort.Assign(1)
		fmt.Printf("Committing transaction for proposal %v\n", proposal.Get())
	} else {
		fmt.Printf("Abording transaction for proposal %v\n", proposal.Get())
	}
	//--end
}

func runServerProtocol(peerAddresses []string) {
	n := gochai.CreateNewNode("c", *myID, *myAddr, peerAddresses, true)
	fmt.Println("Acting as db server.")
	val := gochai.NewVar()
	value := gochai.NewVar()
	value.Assign(0)
	reply := gochai.NewVar()
	// Protocol --
	n.StartSymSet("dbs", "p")
	val = n.Recv()
	fmt.Printf("Received proposal value %v.\n Enter 1 to accept and 0 to refuse.\n", val.Get())
	reply.ReadIO()
	fmt.Printf("decision is: %v\n", reply.Get())
	n.Send(c, reply)
	// -- end
}

// {-@ ensures: and([forall([decl(i,int)], implies(and([elem(i,p), committed=1]), ref(value,i)=prop)), forall([decl(i,int)], implies(and([elem(i,p), committed=0]), ref(value,i)=0))]) -@}
