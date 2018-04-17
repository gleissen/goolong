package main

import (
	"flag"
	"fmt"
	"node"
)

//var id *int = flag.Int("id", 0, "Server id")
//var myAddr *string = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")
//var clientAddr *string = flag.String("clientAddr", ":7071", "Client address (the other machine). Defaults to localhost:7071.")
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
}
