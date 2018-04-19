package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"icetTerm"
	"log"
)

type IceTVisitor struct {
	currentProcId   string
	currentProgram  *icetTerm.Program
	currentProccess *icetTerm.Process
	outPutString    string
}

func main() {
	walkAst()
}

func (v *IceTVisitor) PrettyPrint() string {
	out := v.currentProgram.PrettyPrint()
	if v.currentProccess.Len() > 0 {
		this := v.currentProccess.PrettyPrint()
		out = fmt.Sprintf("%v || %v", this, out)
	}
	return out
}

/*
func (v *IceTVisitor) buildIceTTerm() string {
	//return v.IceTTerm
}
*/
func makeNewIceTVisitor() *IceTVisitor {

	v := &IceTVisitor{"-1",
		icetTerm.NewProgram(),
		icetTerm.NewProcess(),
		""}
	return v
}

func walkAst() {
	// parsing file
	fset := token.NewFileSet()
	node, err := parser.ParseFile(fset, "../pingpong/pingpong.go", nil, parser.ParseComments)
	if err != nil {
		log.Fatal(err)
	}
	v := makeNewIceTVisitor()
	ast.Walk(v, node)
	fmt.Println(v.PrettyPrint())
	//fmt.Printf("Returned IceT term: %v\n", v.IceTTerm)
}

func (v *IceTVisitor) Visit(node ast.Node) (w ast.Visitor) {
	switch node.(type) {
	case *ast.CallExpr:
		// Send
		sendStmt, ok := parseSend(node.(*ast.CallExpr), v.currentProcId)
		if ok {

			v.currentProccess.AddStmt(sendStmt)
		} else {
			// New Node
			proc, ok := parseNewNode(node.(*ast.CallExpr))
			if ok {
				//v.allProcs = append(v.allProcs, v.currentTerm)
				v.currentProgram.AddProc(*v.currentProccess)
				v.currentProcId = proc
				v.currentProccess = icetTerm.NewProcess()
			}
		}
	case *ast.AssignStmt:
		// Recv
		recvStmt, ok := parseRecv(node.(*ast.AssignStmt), v.currentProcId)
		if ok { //recvStmt
			v.currentProccess.AddStmt(recvStmt)
		}
	}
	return v
}

func parseNewNode(site *ast.CallExpr) (string, bool) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "CreateNewNode" {
			proc := site.Args[0].(*ast.BasicLit).Value
			return proc, true
		}
	}
	return "", false
}

func parseSend(site *ast.CallExpr, proc string) (*icetTerm.Send, bool) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "Send" {
			arg1 := site.Args[0].(*ast.BasicLit).Value
			arg2 := site.Args[1].(*ast.BasicLit).Value
			return &icetTerm.Send{ProcID: proc, RecipientID: arg1, Value: arg2}, true
		}
	}
	return nil, false
}

func parseRecv(assign *ast.AssignStmt, proc string) (*icetTerm.Recv, bool) {
	if len(assign.Rhs) == 1 {
		site, ok := assign.Rhs[0].(*ast.CallExpr)
		if ok {
			sel, ok := site.Fun.(*ast.SelectorExpr)
			if ok {
				x, ok := sel.X.(*ast.Ident)
				if ok {
					if sel.Sel.Name == "Recv" && x.Name == "gochai" {
						arg1 := assign.Lhs[0].(*ast.Ident).Name
						return &icetTerm.Recv{ProcID: proc, Variable: arg1}, true
					}
				}
			}
		}
	}
	return nil, false

}
