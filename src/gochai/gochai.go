package gochai

import (
	"node"
)

type ChaiNode struct {
	*node.Node        // extends node
	Set        SymSet //node belongs to set Set
	//StateVars  []StateVar
}

// type StateVar interface {
// 	getType() string
// }

type SymSet struct {
	InSet bool
	Name  string
	Param string
}

// -- protocol state

type IntVar struct {
	thisVar int32
}

func NewIntVar(val int32) IntVar {
	return IntVar{thisVar: val}
}

func (v *IntVar) Assign(val int32) {
	v.thisVar = val
}

func (v *IntVar) Get() int32 {
	return v.thisVar
}

type Map struct {
	thisMap map[int]int
}

func NewMap() Map {
	thisMap := make(map[int]int)
	return Map{thisMap: thisMap}
}

func (m *Map) Put(key int, val int) {
	m.thisMap[key] = val
}

func (m *Map) Get(key int) int {
	return m.thisMap[key]
}

func (m *Map) getType() string {
	return "map(int, int)"
}

// -- protocol communication

func CreateNewNode(name string, id int, myaddr string, peerAddrList []string, isServer bool) *ChaiNode {
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

func EmptySet() SymSet {
	return SymSet{InSet: false, Name: "", Param: ""}
}

// Send sends msg to id
func (n *ChaiNode) Send(id int, msg IntVar) {
	n.NSend(id, msg.thisVar)
}

// Recv blocks until a message is received and then return the receive value
func (n *ChaiNode) Recv() IntVar {
	msg := <-n.MsgChan
	return NewIntVar(msg)
}
