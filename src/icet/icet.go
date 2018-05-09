package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"icetTerm"
	"log"
	"strings"
	"unicode"
)

const COMMENT_SIZE = 5
const ANNOTATION_START = "{-@"
const ANNOTATION_END = "-@}"
const INVARIANT_PREFIX = "invariant:"
const PROPERTY_PREFIX = "ensures:"

type AnnotatationType int

const ( // annotation types
	inv  AnnotatationType = iota
	prop                  = iota
	none                  = iota
)

type IceTVisitor struct {
	currentProcId   string
	currentProgram  *icetTerm.Program
	currentProccess *icetTerm.Process
	currentSet      string
	inSet           bool
	IceTTerm        string
	Comments        ast.CommentMap
	Property        string
	Declarations    icetTerm.Declarations
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
	return fmt.Sprintf("prog(twopc, %v, ensures(%v), %v)", v.Declarations.PrintIceT(), v.Property, v.IceTTerm)
}

func makeNewIceTVisitor(comments ast.CommentMap) *IceTVisitor {
	v := &IceTVisitor{"",
		icetTerm.NewProgram(),
		icetTerm.NewProcess(),
		"",
		false,
		"",
		comments,
		"",
		icetTerm.Declarations{Decls: make([]string, 0)}}
	return v
}

func main() {
	// parsing file
	fset := token.NewFileSet()
	node, err := parser.ParseFile(fset, "../twopc/twopc.go", nil, parser.ParseComments)
	comments := ast.NewCommentMap(fset, node, node.Comments)
	if err != nil {
		log.Fatal(err)
	}
	v := makeNewIceTVisitor(comments)
	v.Property = parseComments(comments.Comments(), prop)
	ast.Walk(v, node)
	fmt.Printf("icet: %v.\n\n pretty print:\n%v \n", v.MakeIceTTerm(), v.PrettyPrint())
}

func (v *IceTVisitor) Visit(node ast.Node) (w ast.Visitor) {
	switch node.(type) {
	case *ast.CallExpr:
		// Send
		sendStmt, ok := parseSend(node.(*ast.CallExpr), v.currentProcId)
		if ok {
			v.currentProccess.AddStmt(sendStmt)
		}
		// New Node
		proc, ok := parseNewNode(node.(*ast.CallExpr))
		if ok {
			v.currentProgram.AddProc(v.currentProccess)
			if v.currentProcId == "" {
				v.currentProcId = proc
			}
			v.currentProccess = icetTerm.NewProcess()
		}
		assignStmt, ok := parseAssign(node.(*ast.CallExpr), v.currentProcId)
		if ok {
			v.currentProccess.AddStmt(assignStmt)
		}
		setName, ok := parseSymAssign(node.(*ast.CallExpr))
		if ok {
			v.currentSet = setName
		}
	case *ast.AssignStmt:
		// Recveive
		recvStmt, ok := parseRecv(node.(*ast.AssignStmt), v.currentProcId)
		if ok {
			v.currentProccess.AddStmt(recvStmt)
		}
		decl, ok := parseDeclaration(node.(*ast.AssignStmt), v.inSet, v.currentSet)
		if ok {
			v.Declarations.Decls = append(v.Declarations.Decls, decl)
		}
	case *ast.RangeStmt:
		// For loop
		parseForLoop(node.(*ast.RangeStmt), v)
		// don't traverse children
		return nil
	case *ast.IfStmt:
		ifStmt, ok := parseConditional(node.(*ast.IfStmt), v)
		if ok {
			v.currentProccess.AddStmt(ifStmt)
			return nil
		}
	case *ast.FuncDecl:
		// symmetric set
		ok := parseSymSetDecl(node.(*ast.FuncDecl), v)
		if ok {
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
	case *ast.CallExpr:
		site, ok := stmt.(*ast.CallExpr)
		if ok {
			sel, ok := site.Fun.(*ast.SelectorExpr)
			if ok && sel.Sel.Name == "Get" {
				return sel.X.(*ast.Ident).Name
			}
		}
		return ""
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

func parseComment(comment *ast.CommentGroup) (string, AnnotatationType) {
	s := comment.Text()
	s = strings.Trim(s, "\n")
	if strings.HasPrefix(s, ANNOTATION_START) && strings.HasSuffix(s, ANNOTATION_END) {
		s = strings.TrimPrefix(s, ANNOTATION_START)
		s = strings.TrimSuffix(s, ANNOTATION_END)
		s = strings.TrimSpace(s)
		if strings.HasPrefix(s, INVARIANT_PREFIX) {
			s = strings.TrimPrefix(s, INVARIANT_PREFIX)
			return s, inv
		} else if strings.HasPrefix(s, PROPERTY_PREFIX) {
			s = strings.TrimPrefix(s, PROPERTY_PREFIX)
			return s, prop
		}
	}
	return "", none
}

func parseComments(comments []*ast.CommentGroup, annotType AnnotatationType) string {
	annotations := make([]string, 0)
	for _, comment := range comments {
		annot, atype := parseComment(comment)
		if atype == annotType {
			annotations = append(annotations, annot)
		}
	}
	return strings.Join(annotations, ",")

}

func parseForLoop(loopTerm *ast.RangeStmt, v *IceTVisitor) {
	domain, ok := loopTerm.X.(*ast.SelectorExpr)
	if ok && domain.Sel.Name == "PeerIds" {
		loopComments := v.Comments.Filter(loopTerm.Body)
		invariant := parseComments(loopComments.Comments(), inv)
		loopVar := loopTerm.Key.(*ast.Ident).Name
		loopVar = strings.ToUpper(loopVar)
		lv := makeNewIceTVisitor(v.Comments)
		lv.currentProcId = v.currentProcId
		ast.Walk(lv, loopTerm.Body)
		v.Declarations.Append(&lv.Declarations)
		LoopStmt := icetTerm.ForLoop{ProcID: v.currentProcId, LoopVar: loopVar, Set: v.currentSet, Invariant: invariant, Stmts: *lv.currentProccess}
		v.currentProccess.AddStmt(&LoopStmt)
	}
}

func parseAssign(site *ast.CallExpr, proc string) (*icetTerm.Assign, bool) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "Assign" {
			variable := sel.X.(*ast.Ident).Name
			value := getValue(site.Args[0])
			return &icetTerm.Assign{ProcID: proc, Var: variable, Value: value}, true
		}
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

func parseSymSetDecl(decl *ast.FuncDecl, v *IceTVisitor) bool {
	for _, stmt := range decl.Body.List {
		stmt, ok := stmt.(*ast.ExprStmt)
		if ok {
			stmt, ok := stmt.X.(*ast.CallExpr)
			if ok {
				set, ok := parseStartSymSet(stmt)
				if ok {
					sv := makeNewIceTVisitor(v.Comments)
					sv.currentSet = set.Name
					sv.inSet = true
					sv.currentProcId = set.ProcVar
					ast.Walk(sv, decl.Body)
					v.Declarations.Append(&sv.Declarations)
					v.currentProgram.AddProc(set)
					v.Declarations.AppendDecl(fmt.Sprintf("decl(%v,set)", set.Name))
					set.Stmts = *sv.currentProccess
					return true
				}
			}
		}
	}
	return false
}

func parseSymAssign(site *ast.CallExpr) (string, bool) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "AssignSymSet" {
			return getValue(site.Args[0]), true
		}
	}
	return "", false
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

func parseDeclaration(assign *ast.AssignStmt, inSet bool, setName string) (string, bool) {
	if len(assign.Rhs) == 1 {
		site, ok := assign.Rhs[0].(*ast.CallExpr)
		if ok {
			sel, ok := site.Fun.(*ast.SelectorExpr)
			if ok {
				if sel.Sel.Name == "NewVar" {
					varName := assign.Lhs[0].(*ast.Ident).Name
					if inSet {
						return fmt.Sprintf("decl(%v, map(set(%v), int))", varName, setName), true
					}
					return fmt.Sprintf("decl(%v, int)", varName), true
				}
			}
		}
	}
	return "", false
}

func parseRecv(assign *ast.AssignStmt, proc string) (*icetTerm.Recv, bool) {
	if len(assign.Rhs) == 1 {
		site, ok := assign.Rhs[0].(*ast.CallExpr)
		if ok {
			sel, ok := site.Fun.(*ast.SelectorExpr)
			if ok {
				arg1 := assign.Lhs[0].(*ast.Ident).Name
				if sel.Sel.Name == "Recv" {
					return &icetTerm.Recv{ProcID: proc, Variable: arg1, IsRecvFrom: false}, true
				} else if sel.Sel.Name == "RecvFrom" {
					id := site.Args[0].(*ast.Ident).Name
					return &icetTerm.Recv{ProcID: proc, Variable: arg1, FromId: id, IsRecvFrom: true}, true
				}
			}
		}
	}
	return nil, false

}

/*
ProcID string
Cond   string
Left   Process
Right  Process
*/

// parsing conditionals
func parseConditional(ifStmt *ast.IfStmt, v *IceTVisitor) (*icetTerm.Conditional, bool) {
	//parse condition
	cond := parseCondition(ifStmt.Cond, v)
	// parse left subexpression
	vl := makeNewIceTVisitor(v.Comments)
	vl.currentProcId = v.currentProcId
	ast.Walk(vl, ifStmt.Body)
	// parse right subexpression
	var rightproc *icetTerm.Process
	if ifStmt.Else != nil {
		vr := makeNewIceTVisitor(v.Comments)
		vr.currentProcId = v.currentProcId
		ast.Walk(vr, ifStmt.Else)
		rightproc = vr.currentProccess
	} else {
		rightproc = icetTerm.NewProcess()
	}
	if !vl.currentProccess.IsEmpty() {
		return &icetTerm.Conditional{ProcID: v.currentProcId, Cond: cond, Left: *vl.currentProccess, Right: *rightproc}, true
	}
	return nil, false
}

func parseCondition(cond ast.Expr, v *IceTVisitor) string {
	switch cond.(type) {
	case *ast.BinaryExpr:
		binExp := cond.(*ast.BinaryExpr)
		left := parseCondition(binExp.X, v)
		right := parseCondition(binExp.Y, v)
		if binExp.Op.String() == "==" {
			return fmt.Sprintf("%v=%v", left, right)
		}
	default:
		val := getValue(cond)
		if v.inSet && !isInt(val) {
			val = fmt.Sprintf("ref(%v,%v)", val, v.currentProcId)
		}
		return val
	}
	return "ndet"
}

func isInt(s string) bool {
	for _, c := range s {
		if !unicode.IsDigit(c) {
			return false
		}
	}
	return true
}
