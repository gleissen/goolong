package multiproto

import (
	"bufio"
	"clientproto"
	"fastrpc"
	"fmt"
	"gochai"
	"io"
	"log"
	"net"
	"state"
)

const CHAN_BUFFER_SIZE = 200000

const (
	PrepareType uint8 = 0
	AcceptType        = 1
)

type Propose struct {
	*clientproto.Propose
	Wire *bufio.Writer
}

type Prepare struct {
	id   uint8
	t    int32
	inst int32
}

type AcceptorReply struct {
	Success uint8
	Rwt     int32
	Rw      int32
}

type Accept struct {
	id      uint8
	t       int32
	x       int32
	inst    int32
	Command []state.Command
}

type PaxosNode struct {
	*gochai.ChaiNode // extends ChaiNode
	prepareRPC       uint8
	prepareChans     []chan fastrpc.Serializable
	acceptRPC        uint8
	acceptChans      []chan fastrpc.Serializable
	replyRPC         uint8
	replyChans       []chan fastrpc.Serializable
	ProposeChan      chan *Propose // channel for client proposals
	State            *state.State
	CrtInstance      int32
}

func NewPaxosNode(name string, id int, myaddr string, peerAddrList []string, isServer bool) *PaxosNode {
	n := &PaxosNode{
		gochai.CreateNewNode(name, id, myaddr, peerAddrList, isServer),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList)),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList)),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList)),
		make(chan *Propose, CHAN_BUFFER_SIZE),
		state.InitState(),
		0}

	n.prepareRPC = n.RegisterRPC(new(Prepare), n.prepareChans)
	n.acceptRPC = n.RegisterRPC(new(Accept), n.acceptChans)
	n.replyRPC = n.RegisterRPC(new(AcceptorReply), n.replyChans)
	for i := range n.prepareChans {
		n.prepareChans[i] = make(chan fastrpc.Serializable)
		n.acceptChans[i] = make(chan fastrpc.Serializable)
		n.replyChans[i] = make(chan fastrpc.Serializable)
	}
	return n
}

func (n *PaxosNode) Run() {
	fmt.Printf("Starting.\n")
	n.Start()
	fmt.Printf("Done starting.\n")
	if !n.IsServer {
		go n.WaitForClientConnections()
	}
}

func (n *PaxosNode) MakeUniqueBallot(ballot int32) int32 {
	return (ballot << 4) | n.MyId()
}

// =================
//  Peer connections
// =================

// Sending and Receiving
func (n *PaxosNode) SendPrepare(id int, repId *gochai.UInt8, term *gochai.IntVar, inst *gochai.IntVar) {
	msg := &Prepare{id: repId.Get(), t: term.Get(), inst: inst.Get()}
	n.NSend(id, n.prepareRPC, msg)
}

func (n *PaxosNode) SendAccept(id int, repId *gochai.UInt8, term *gochai.IntVar, val *gochai.IntVar, inst *gochai.IntVar, proposal *Propose) {
	cmd := new([]state.Command)
	*cmd = append(*cmd, proposal.Command)
	msg := &Accept{id: repId.Get(), t: term.Get(), x: val.Get(), inst: inst.Get(), Command: *cmd}
	n.NSend(id, n.acceptRPC, msg)
}

func (n *PaxosNode) AcceptorReceive() (msgType *gochai.UInt8, id *gochai.UInt8, instance *gochai.IntVar, term *gochai.IntVar, value *gochai.IntVar) {
	allChans := n.prepareChans
	allChans = append(allChans, n.acceptChans...)
	msg := n.RecvAll(allChans)
	switch msg.(type) {
	case *Prepare:
		prep := msg.(*Prepare)
		return gochai.NewUInt8_(PrepareType), gochai.NewUInt8_(prep.id), gochai.NewIntVar_(prep.inst), gochai.NewIntVar_(prep.t), gochai.NewIntVar_(-1)
	case *Accept:
		acc := msg.(*Accept)
		return gochai.NewUInt8_(AcceptType), gochai.NewUInt8_(acc.id), gochai.NewIntVar_(acc.inst), gochai.NewIntVar_(acc.t), gochai.NewIntVar_(acc.x)
	}
	return nil, nil, nil, nil, nil
}

func (n *PaxosNode) SendAcceptorReply(id int, rwt int32, rw int32, success uint8) {
	msg := &AcceptorReply{Rwt: rwt, Rw: rw, Success: success}
	n.NSend(id, n.replyRPC, msg)
}

func (n *PaxosNode) RecvAcceptorReplyFrom(id int) (*gochai.IntVar, *gochai.IntVar, *gochai.UInt8) {
	msg := n.RecvFromGen(id, n.replyChans).(*AcceptorReply)
	return gochai.NewIntVar_(msg.Rwt), gochai.NewIntVar_(msg.Rw), gochai.NewUInt8_(msg.Success)
}

// ====================
//  Client connections
// ====================

/* Client connections dispatcher */
func (n *PaxosNode) WaitForClientConnections() {
	fmt.Printf("Waiting for connections...\n")
	for !n.Stop {
		conn, err := n.Listener.Accept()
		if err != nil {
			log.Println("Accept error:", err)
			continue
		}
		fmt.Printf("Accepted connection from: %v\n", conn.RemoteAddr())
		go n.clientListener(conn)
	}
}

func (n *PaxosNode) clientListener(conn net.Conn) {
	reader := bufio.NewReader(conn)
	writer := bufio.NewWriter(conn)
	var msgType byte
	var err error
	for !n.Stop && err == nil {

		if msgType, err = reader.ReadByte(); err != nil {
			break
		}
		switch uint8(msgType) {

		case clientproto.PROPOSE:
			prop := new(clientproto.Propose)
			if err = prop.Unmarshal(reader); err != nil {
				break
			}
			n.ProposeChan <- &Propose{prop, writer}
			break

		}
	}
	if err != nil && err != io.EOF {
		log.Println("Error when reading from client connection:", err)
	}
}

func (n *PaxosNode) ReplyPropose(reply *clientproto.ProposeReply, w *bufio.Writer) {
	reply.Marshal(w)
	w.Flush()
}
