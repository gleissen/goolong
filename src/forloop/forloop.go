package main

import (
	"flag"
	"fmt"
	"gochai"
)

var isServer = flag.Bool("server", true, "Act as server (true) or client (false). ")
var myID = flag.Int("id", 0, "Replica id")
var myAddr = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")

func main() {
	flag.Parse()
	peerAddresses := flag.Args()
	if *isServer {
		runServerProtocol(peerAddresses)
	} else {
		runClientProtocol(peerAddresses)
	}
}

func runServerProtocol(peerAddresses []string) {
	n := gochai.CreateNewNode(0, *myAddr, peerAddresses, false)
	n.AssignSymSet("clients", "")
	fmt.Println("Acting as server.")
	//Protocol--
	for id := range n.PeerIds {
		fmt.Printf("sending 42 to %v\n", id)
		n.Send(id, 42)
	}
	//--end
}

func runClientProtocol(peerAddresses []string) {
	n := gochai.CreateNewNode(*myID, *myAddr, peerAddresses, true)
	fmt.Println("Acting as client.")
	// Protocol --
	n.StartSymSet("clients", "p")
	msg := n.Recv()
	fmt.Printf("Received Message: %v", msg)
	// -- end
}
