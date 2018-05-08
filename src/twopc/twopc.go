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
	n.AssignSymSet("dbs", "")
	fmt.Println("Acting as coordinator.\n")
	proposal := gochai.NewVar()
	decision := gochai.NewVar()
	abort := gochai.NewVar()
	abort.Assign(0)
	//Protocol--
	for ID := range n.PeerIds {
		// {-@ invariant: ? -@}
		fmt.Printf("Sending proposal to %v\n", ID)
		n.Send(ID, proposal)
		decision = n.Recv()
		fmt.Printf("Received %v\n", decision.Get())
		if decision.Get() == 1 {
			abort.Assign(1)
		}
	}
	if decision.Get() == 1 {
		fmt.Printf("Committing transaction for proposal %v\n", proposal.Get())
	} else {
		fmt.Printf("Abording transaction for proposal %v\n", proposal.Get())
	}

	//--end
}

func runServerProtocol(peerAddresses []string) {
	n := gochai.CreateNewNode("c", *myID, *myAddr, peerAddresses, true)
	fmt.Println("Acting as db server.")
	proposal := gochai.NewVar()
	reply := gochai.NewVar()
	// Protocol --
	n.StartSymSet("dbs", "p")
	proposal = n.Recv()
	fmt.Printf("Received proposal value %v.\n Enter 1 to accept and 0 to refuse.\n", proposal.Get())
	reply.ReadIO()
	n.Send(c, proposal)
	// -- end
}

// {-@ ensures: forall([decl(p,int)], implies(elem(p, clients), ref(msg, p)=42)) -@}
