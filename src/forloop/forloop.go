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
	n := gochai.CreateNewNode(*myID, *myAddr, peerAddresses, false)
	fmt.Println("Acting as server.")
	fmt.Println("Broadcasting 42.")

	// Protocol--
	for id := range n.PeerIds {
		n.Send(id, 42)
	}
	// --end
}

func runClientProtocol(peerAddresses []string) {
	fmt.Println("Acting as client.")
	n := gochai.CreateNewNode(*myID, *myAddr, peerAddresses, true)
	msg := gochai.Recv(n)
	fmt.Printf("Received Message: %v", msg)
}
