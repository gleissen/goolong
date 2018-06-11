package paxosproto

import (
	"fastrpc"
	"gochai"
)

type ProposalReply struct {
	Success uint8
	Rwt     int32
	Rw      int32
}

func (p *ProposalReply) New() fastrpc.Serializable {
	return &ProposalReply{0, 0, 0}
}

type PaxosNode struct {
	*gochai.ChaiNode // extends ChaiNode
	proposalType     uint8
	proposalChans    []chan fastrpc.Serializable
	acceptanceType   uint8
	acceptanceChans  []chan fastrpc.Serializable
}

func NewPaxosNode(name string, id int, myaddr string, peerAddrList []string, isServer bool) *PaxosNode {
	n := &PaxosNode{
		gochai.CreateNewNode(name, id, myaddr, peerAddrList, isServer),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList)),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList))}

	// TODO: other types
	n.proposalType = n.RegisterRPC(new(ProposalReply), n.proposalChans)
	for i := range n.proposalChans {
		n.proposalChans[i] = make(chan fastrpc.Serializable)
	}

	return n
}

// Sending and Receiving
func (n *PaxosNode) SendPropReply(id int, rwt *gochai.IntVar, rw *gochai.IntVar, success *gochai.BoolVar) {
	msg := &ProposalReply{Rwt: rwt.Get(), Rw: rw.Get(), Success: success.Get()}
	n.NSend(id, n.proposalType, msg)
}

func (n *PaxosNode) RecvPropReplyFrom(id int) (*gochai.IntVar, *gochai.IntVar, *gochai.BoolVar) {
	msg := n.RecvFromGen(id, n.proposalChans).(*ProposalReply)
	return gochai.NewIntVar_(msg.Rwt), gochai.NewIntVar_(msg.Rw), gochai.NewBoolVar_(msg.Success)
}
