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
	l := gochai.NewVar()
	l.Assign(42)
	r := gochai.NewVar()
	r.Assign(1)
	pair := gochai.MakePair(l, r)
	fmt.Printf("Acting as client %v. Sending  pair %v, %v \n", n.Id, pair.L.Get(), pair.R.Get())
	n.Send(0, pair)
	n.Shutdown()
}

func runServerProtocol() {
	fmt.Println("Acting as server.")
	n := gochai.CreateNewNode("m", 0, ":7070", []string{":7071"}, true)
	l, r := n.RecvPair()
	fmt.Printf("Received pair: %v, %v", l.Get(), r.Get())
	n.Shutdown()
}
