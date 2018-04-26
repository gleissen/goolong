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
	currentSet      string
	IceTTerm        string
}

func (v *IceTVisitor) PrettyPrint() string {
	out := v.currentProgram.PrettyPrint()
	if v.currentProccess.Len() > 0 {
		this := v.currentProccess.PrettyPrint()
		out = fmt.Sprintf("%v || %v", this, out)
	}
	return out
}

func (v *IceTVisitor) MakeIceTTerm() string {
	v.currentProgram.AddProc(v.currentProccess)
	v.IceTTerm = v.currentProgram.PrintIceT()
	v.currentProgram.RemoveLastProc()
	return v.IceTTerm
}

func makeNewIceTVisitor() *IceTVisitor {

	v := &IceTVisitor{"",
		icetTerm.NewProgram(),
		icetTerm.NewProcess(),
		"",
		""}
	return v
}

func main() {
	// parsing file
	fset := token.NewFileSet()
	node, err := parser.ParseFile(fset, "../forloop/forloop.go", nil, parser.ParseComments)
	//node, err := parser.ParseFile(fset, "../pingpong/pingpong.go", nil, parser.ParseComments)
	if err != nil {
		log.Fatal(err)
	}
	v := makeNewIceTVisitor()
	ast.Walk(v, node)
	fmt.Printf("proccess: %v\n icet-t: %v\n", v.PrettyPrint(), v.MakeIceTTerm())
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
				v.currentProgram.AddProc(v.currentProccess)
				if v.currentProcId == "" {
					v.currentProcId = proc
				}
				v.currentProccess = icetTerm.NewProcess()
			}
		}
	case *ast.AssignStmt:
		// Recveive
		recvStmt, ok := parseRecv(node.(*ast.AssignStmt), v.currentProcId)
		if ok {
			fmt.Printf("parsing receive with proc: %v and internal proc: %v\n", v.currentProcId, recvStmt.ProcID)
			v.currentProccess.AddStmt(recvStmt)
		}
	case *ast.RangeStmt:
		// For loop
		LoopStmt, ok := parseForLoop(node.(*ast.RangeStmt), v.currentProcId)
		if ok {
			v.currentProccess.AddStmt(LoopStmt)
		}
		// don't traverse children
		return nil
	case *ast.FuncDecl:
		// symmetric set
		set, ok := parseSymSetDecl(node.(*ast.FuncDecl))
		if ok {
			v.currentProgram.AddProc(set)
			return nil
		}
	}
	return v
}

func stringRemoveQuotes(s string) string {
	if len(s) > 0 {
		if s[0] == '"' {
			s = s[1:]
		}
		if s[len(s)-1] == '"' {
			s = s[:len(s)-1]
		}
	}
	return s
}

func getValue(stmt ast.Node) string {
	switch stmt.(type) {
	case *ast.BasicLit:
		return stringRemoveQuotes(stmt.(*ast.BasicLit).Value)
	case *ast.Ident:
		return stringRemoveQuotes(stmt.(*ast.Ident).Name)
	default:
		return ""
	}
}

func parseNewNode(site *ast.CallExpr) (string, bool) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "CreateNewNode" {
			proc := getValue(site.Args[0])
			return proc, true
		}
	}
	return "", false
}

func parseForLoop(loopTerm *ast.RangeStmt, proc string) (*icetTerm.ForLoop, bool) {
	domain, ok := loopTerm.X.(*ast.SelectorExpr)
	if ok && domain.Sel.Name == "PeerIds" {
		loopVar := loopTerm.Key.(*ast.Ident).Name
		lv := makeNewIceTVisitor()
		lv.currentProcId = proc
		ast.Walk(lv, loopTerm.Body)
		return &icetTerm.ForLoop{ProcID: proc, LoopVar: loopVar, Set: "clients", Stmts: *lv.currentProccess}, true
	}
	return nil, false
}

func parseSend(site *ast.CallExpr, proc string) (*icetTerm.Send, bool) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "Send" {
			arg1 := getValue(site.Args[0])
			arg2 := getValue(site.Args[1])
			return &icetTerm.Send{ProcID: proc, RecipientID: arg1, Value: arg2}, true
		}
	}
	return nil, false
}

func parseSymSetDecl(decl *ast.FuncDecl) (*icetTerm.SymSet, bool) {
	for _, stmt := range decl.Body.List {
		stmt, ok := stmt.(*ast.ExprStmt)
		if ok {
			stmt, ok := stmt.X.(*ast.CallExpr)
			if ok {
				set, ok := parseStartSymSet(stmt)
				if ok {
					fmt.Printf("decending with set name: %v and proc:%v\n", set.Name, set.ProcVar)
					sv := makeNewIceTVisitor()
					sv.currentSet = set.Name
					sv.currentProcId = set.ProcVar
					ast.Walk(sv, decl.Body)
					fmt.Printf("done descending.\n")
					set.Stmts = *sv.currentProccess
					return set, true
				}
			}
		}
	}
	return nil, false
}

func parseStartSymSet(site *ast.CallExpr) (*icetTerm.SymSet, bool) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "StartSymSet" {
			procVar := getValue(site.Args[1])
			setName := getValue(site.Args[0])
			set := icetTerm.SymSet{ProcVar: procVar, Name: setName, Stmts: *icetTerm.NewProcess()}
			return &set, true
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
				if sel.Sel.Name == "Recv" {
					arg1 := assign.Lhs[0].(*ast.Ident).Name
					return &icetTerm.Recv{ProcID: proc, Variable: arg1}, true
				}
			}
		}
	}
	return nil, false

}
