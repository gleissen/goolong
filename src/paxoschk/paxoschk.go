package main

import (
	"flag"
	"fmt"
	"go/ast"
	"icet"
	"icetTerm"
	"log"
)

// Parses paxos specific sends and receive methods
type PaxosParser struct{}

func (p *PaxosParser) ParseSend(name string, args []ast.Expr, procID string, idType icetTerm.IDType, getValue func(ast.Node) string) (bool, icetTerm.IcetTerm) {
	//n.SendAcceptorReply(int(resID.Get()), wT, w, success)
	if name == "SendAcceptorReply" {
		id := getValue(args[0])
		wt := getValue(args[1])
		w := getValue(args[2])
		success := getValue(args[3])
		val := fmt.Sprintf("pair(%v,pair(%v,%v))", wt, w, success)
		return true, &icetTerm.Send{ProcID: procID, RecipientID: id, RecipientType: idType, Value: val}
	}
	//n.SendPrepare(Peer, id, myTerm)
	if name == "SendPrepare" {
		peerID := getValue(args[0])
		myID := getValue(args[1])
		myTerm := getValue(args[2])
		val := fmt.Sprintf("pair(%v,%v)", myID, myTerm)
		return true, &icetTerm.Send{ProcID: procID, RecipientID: peerID, RecipientType: idType, Value: val}
	}
	//n.SendAccept(Peer, id, myTerm, x)
	if name == "SendAccept" {
		peerID := getValue(args[0])
		myID := getValue(args[1])
		myTerm := getValue(args[2])
		x := getValue(args[3])
		val := fmt.Sprintf("pair(%v,pair(%v,%v))", myID, myTerm, x)
		return true, &icetTerm.Send{ProcID: procID, RecipientID: peerID, RecipientType: idType, Value: val}
	}
	return false, nil
}

func (p *PaxosParser) ParseReceive(name string, args []ast.Expr, fromID string, procID string, bool, getValue func(ast.Node) string) (bool, icetTerm.IcetTerm) {
	//rwT, rw, rsuccess := n.RecvAcceptorReplyFrom(Peer)
	if name == "RecvAcceptorReplyFrom" {
		rwT := getValue(args[0])
		rw := getValue(args[1])
		rsuccess := getValue(args[2])
		val := fmt.Sprintf("pair(%v,pair(%v,%v))", rwT, rw, rsuccess)
		v.currentProccess.AddStmt(&icetTerm.Recv{ProcID: procID, Variable: val, FromId: fromID, IsRecvFrom: true})
	}
	return false, nil
}

func main() {
	// parsing file
	flag.Parse()
	if flag.NArg() != 1 {
		log.Fatal("usage: icet <go file>")
	}
	file := flag.Args()[0]
	v := icet.MakeNewIceTVisitor()
	v.Parser = &PaxosParser{}
	term := v.ExtractIcetTerm(file)
	fmt.Printf("%v.", term)
}
