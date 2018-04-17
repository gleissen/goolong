package main

import (
	"flag"
	"fmt"
	"node"
)

var server = flag.Bool("server", true, "Act as server (true) or client (false). ")

func main() {
	flag.Parse()
	var n *node.Node
	if *server {
		n = node.MakeNode(0, ":7070", []string{":7071"})
		fmt.Println("Acting as server.")
	} else {
		n = node.MakeNode(1, ":7071", []string{":7070"})
		fmt.Println("Acting as client.")
	}
	fmt.Println("Connecting to clients")
	connected := make(chan bool)
	go n.Run(connected)
	<-connected

	// Run protocol
	if *server {
		n.Send(0, 42)
	} else {
		msg := <-n.MsgChan
		fmt.Printf("Received Message: %v", msg)
	}
}
