package gochai

import (
	"node"
)

type ChaiNode struct {
	*node.Node        // extends node
	Set        SymSet //node belongs to set Set
}

type SymSet struct {
	InSet bool
	Name  string
	Param string
}

func CreateNewNode(id int, myaddr string, peerAddrList []string, isServer bool) *ChaiNode {
	n := &ChaiNode{
		node.MakeNode(id, myaddr, peerAddrList, isServer),
		EmptySet()}
	n.Run()
	<-n.Connected
	return n
}

func (n *ChaiNode) AssignSymSet(name string, param string) {
	n.Set = SymSet{InSet: false, Name: name, Param: param}
}

func (n *ChaiNode) StartSymSet(name string, param string) {
	n.Set = SymSet{InSet: true, Name: name, Param: param}
}

func (n *ChaiNode) EndSymSet() {
	// this is just for extracting terms
}

func EmptySet() SymSet {
	return SymSet{InSet: false, Name: "", Param: ""}
}

// Send sends msg to id
func (n *ChaiNode) Send(id int, msg int32) {
	n.NSend(id, msg)
}

// Recv blocks until a message is received and then return the receive value
func (n *ChaiNode) Recv() int32 {
	msg := <-n.MsgChan
	return msg
}
