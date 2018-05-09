package gochai

import (
	"fmt"
	"node"
	"reflect"
)

type ChaiNode struct {
	*node.Node        // extends node
	Set        SymSet //node belongs to set Set
	//StateVars  []StateVar
}

type SymSet struct {
	InSet bool
	Name  string
	Param string
}

// -- protocol state

type IntVar struct {
	thisVar int32
}

type BoolVar struct {
	thisVar bool
}

func NewVar() IntVar {
	return IntVar{thisVar: -1}
}

func (v *IntVar) Assign(val int32) {
	v.thisVar = val
}

func (v *IntVar) Get() int32 {
	return v.thisVar
}

// -- get user input from stdin
func (v *IntVar) ReadIO() {
	fmt.Scanf("%v", &v.thisVar)
}

func NewBoolVar() BoolVar {
	return BoolVar{thisVar: false}
}

func (v *BoolVar) Assign(val bool) {
	v.thisVar = val
}

func (v *BoolVar) Get() bool {
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

func (n *ChaiNode) Shutdown() {
	n.Done <- true
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
	fmt.Printf("Sending msg %v to %v\n", msg.Get(), id)
	n.NSend(id, msg.thisVar)
}

// Recv blocks until a message  from any peer is received,
// and returns the receive value.
func (n *ChaiNode) Recv() IntVar {
	cases := make([]reflect.SelectCase, n.N)
	for i, ch := range n.MsgChans {
		cases[i] = reflect.SelectCase{Dir: reflect.SelectRecv, Chan: reflect.ValueOf(ch)}
	}
	chosen, value, _ := reflect.Select(cases)
	msg := int32(value.Int())
	fmt.Printf("received %v from %v\n", msg, chosen)
	v := NewVar()
	v.Assign(msg)
	return v
}

// Receive from a given id
func (n *ChaiNode) RecvFrom(id int) IntVar {
	fmt.Printf("waiting for message from %v\n", id)
	msg := <-n.MsgChans[id]
	fmt.Printf("received msg %v from %v\n", msg, id)
	v := NewVar()
	v.Assign(msg)
	return v
}
