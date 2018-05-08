package main

import (
	"flag"
	"fmt"
	"gochai"
)

var server = flag.Bool("server", true, "Act as server (true) or client (false). ")

func main() {
	flag.Parse()
	if *server {
		runServerProtocol()
	} else {
		runClientProtocol()
	}
}

func runClientProtocol() {
	n := gochai.CreateNewNode("c", 1, ":7071", []string{":7070"}, false)
	val := gochai.NewVar()
	val.Assign(42)
	fmt.Printf("Acting as client %v.", n.Id)
	n.Send(0, val)
}

func runServerProtocol() {
	fmt.Println("Acting as server.")
	n := gochai.CreateNewNode("m", 0, ":7070", []string{":7071"}, true)
	msg := n.Recv()
	fmt.Printf("Received Message: %v", msg.Get())
}
