package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"icetTerm"
	"log"
	"strings"
)

const COMMENT_SIZE = 5
const ANNOTATION_START = "{-@"
const ANNOTATION_END = "-@}"
const INVARIANT_TYPE = "invariant:"

type IceTVisitor struct {
	currentProcId   string
	currentProgram  *icetTerm.Program
	currentProccess *icetTerm.Process
	currentSet      string
	IceTTerm        string
	Comments        ast.CommentMap
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

func makeNewIceTVisitor(comments ast.CommentMap) *IceTVisitor {

	v := &IceTVisitor{"",
		icetTerm.NewProgram(),
		icetTerm.NewProcess(),
		"",
		"",
		comments}
	return v
}

func main() {
	// parsing file
	fset := token.NewFileSet()
	node, err := parser.ParseFile(fset, "../forloop/forloop.go", nil, parser.ParseComments)
	comments := ast.NewCommentMap(fset, node, node.Comments)
	if err != nil {
		log.Fatal(err)
	}
	v := makeNewIceTVisitor(comments)
	ast.Walk(v, node)
	//fmt.Printf("proccess: %v\n icet-t: %v\n", v.PrettyPrint(), v.MakeIceTTerm())
	fmt.Printf("icet-t: %v\n", v.MakeIceTTerm())
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
			v.currentProccess.AddStmt(recvStmt)
		}
	case *ast.RangeStmt:
		// For loop
		LoopStmt, ok := parseForLoop(node.(*ast.RangeStmt), v.currentProcId, v.Comments)
		if ok {
			v.currentProccess.AddStmt(LoopStmt)
		}
		// don't traverse children
		return nil
	case *ast.FuncDecl:
		// symmetric set
		set, ok := parseSymSetDecl(node.(*ast.FuncDecl), v.Comments)
		if ok {
			v.currentProgram.AddProc(set)
			return nil
		}
		// case *ast.CommentGroup:
		// 	c := node.(*ast.CommentGroup)
		// 	fmt.Printf("found comment %v\n", c.Text())
		// 	v.Comments = append(v.Comments, *c)
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

func parseComment(comment *ast.CommentGroup) string {
	s := comment.Text()
	s = strings.Trim(s, "\n")
	if strings.HasPrefix(s, ANNOTATION_START) && strings.HasSuffix(s, ANNOTATION_END) {
		s = strings.TrimPrefix(s, ANNOTATION_START)
		s = strings.TrimSuffix(s, ANNOTATION_END)
		s = strings.TrimSpace(s)
		if strings.HasPrefix(s, INVARIANT_TYPE) {
			s = strings.TrimPrefix(s, INVARIANT_TYPE)
		}
		return strings.TrimSpace(s)
	}
	return ""
}

func parseComments(comments []*ast.CommentGroup) string {
	invariant := ""
	for _, comment := range comments {
		invariant = invariant + parseComment(comment)
	}
	return invariant
}

func parseForLoop(loopTerm *ast.RangeStmt, proc string, comments ast.CommentMap) (*icetTerm.ForLoop, bool) {
	domain, ok := loopTerm.X.(*ast.SelectorExpr)
	if ok && domain.Sel.Name == "PeerIds" {
		loopComments := comments.Filter(loopTerm.Body)
		invariant := parseComments(loopComments.Comments())
		loopVar := loopTerm.Key.(*ast.Ident).Name
		loopVar = strings.ToUpper(loopVar)
		lv := makeNewIceTVisitor(comments)
		lv.currentProcId = proc
		ast.Walk(lv, loopTerm.Body)
		return &icetTerm.ForLoop{ProcID: proc, LoopVar: loopVar, Set: "clients", Invariant: invariant, Stmts: *lv.currentProccess}, true
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

func parseSymSetDecl(decl *ast.FuncDecl, comments ast.CommentMap) (*icetTerm.SymSet, bool) {
	for _, stmt := range decl.Body.List {
		stmt, ok := stmt.(*ast.ExprStmt)
		if ok {
			stmt, ok := stmt.X.(*ast.CallExpr)
			if ok {
				set, ok := parseStartSymSet(stmt)
				if ok {
					sv := makeNewIceTVisitor(comments)
					sv.currentSet = set.Name
					sv.currentProcId = set.ProcVar
					ast.Walk(sv, decl.Body)
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
			procVar := strings.ToUpper(getValue(site.Args[1]))
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
