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
	n := gochai.CreateNewNode(1, ":7071", []string{":7070"})
	fmt.Println("Acting as client.")
	n.Send(0, 42)
}

func runServerProtocol() {
	fmt.Println("Acting as server.")
	n := gochai.CreateNewNode(0, ":7070", []string{":7071"})
	msg := gochai.Recv(n)
	fmt.Printf("Received Message: %v", msg)
}
