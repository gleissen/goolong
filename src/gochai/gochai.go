package gochai

import "fmt"
import "node"

func CreateNewNode(id int, myaddr string, peerAddrList []string, isServer bool) *node.Node {
	n := node.MakeNode(id, myaddr, peerAddrList, isServer)
	n.Run()
	<-n.Connected
	return n
}

// Send sends msg to id
func Send(id int, msg int32, n *node.Node) {
	fmt.Printf("sending %v to %v\n", id, msg)
	n.Send(id, msg)
}

// Recv blocks until a message is received and then return the receive value
func Recv(n *node.Node) int32 {
	msg := <-n.MsgChan
	fmt.Printf("received %v \n", msg)
	return msg
}

// TODO
func Broadcast(addr []int, msg int) {
	//TODO
}
