package main

import (
	"flag"
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
const NDET = "ndet"

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
	return fmt.Sprintf("prog(raftcore, %v, ensures(%v), %v)", v.Declarations.PrintIceT(), v.Property, v.IceTTerm)
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
	flag.Parse()
	if flag.NArg() != 1 {
		log.Fatal("usage: icet <go file>")
	}
	file := flag.Args()[0]

	fset := token.NewFileSet()
	node, err := parser.ParseFile(fset, file, nil, parser.ParseComments)
	comments := ast.NewCommentMap(fset, node, node.Comments)
	if err != nil {
		log.Fatal(err)
	}
	v := makeNewIceTVisitor(comments)
	v.Property = parseComments(comments.Comments(), prop)
	ast.Walk(v, node)
	//fmt.Printf("icet: %v.\n\n pretty print:\n%v \n", v.MakeIceTTerm(), v.PrettyPrint())
	fmt.Printf("%v.", v.MakeIceTTerm())
}

func (v *IceTVisitor) Visit(node ast.Node) (w ast.Visitor) {
	switch node.(type) {

	case *ast.CallExpr:
		// Send
		parseSend(node.(*ast.CallExpr), v)
		// New Node
		parseNewNode(node.(*ast.CallExpr), v)
		// Assignments
		parseAssign(node.(*ast.CallExpr), v)
		// Assigning a symmetric proccess to communicate with
		parseSymAssign(node.(*ast.CallExpr), v)

	case *ast.AssignStmt:
		// Recveive
		parseRecv(node.(*ast.AssignStmt), v)
		// New variables declaration
		parseDeclaration(node.(*ast.AssignStmt), v)

	case *ast.RangeStmt:
		// For loop
		ok := parseForLoop(node.(*ast.RangeStmt), v)
		if ok {
			return nil // children were already traversed
		}

	case *ast.IfStmt:
		ok := parseConditional(node.(*ast.IfStmt), v)
		if ok {
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

func getValue(stmt ast.Node, v *IceTVisitor) string {
	switch stmt.(type) {
	case *ast.BasicLit:
		return stringRemoveQuotes(stmt.(*ast.BasicLit).Value)
	case *ast.Ident:
		return stringRemoveQuotes(stmt.(*ast.Ident).Name)
	case *ast.CallExpr:
		site := stmt.(*ast.CallExpr)
		switch site.Fun.(type) {
		case *ast.SelectorExpr:
			sel := site.Fun.(*ast.SelectorExpr)
			if sel.Sel.Name == "Get" {
				return sel.X.(*ast.Ident).Name
			}
			if sel.Sel.Name == "MyId" {
				return v.currentProcId
			}
			if sel.Sel.Name == "NumPeers" {
				return fmt.Sprintf("card(%v)", v.currentSet)
			}
		case *ast.Ident:
			ident := site.Fun.(*ast.Ident)
			if ident.Name == "int" {
				return getValue(site.Args[0], v)
			}
			return ident.Name
		default:
			return NDET
		}

	case *ast.BinaryExpr:
		binExp := stmt.(*ast.BinaryExpr)
		e1 := getValue(binExp.X, v)
		e2 := getValue(binExp.Y, v)
		return fmt.Sprintf("%v %v %v", e1, binExp.Op.String(), e2)

	default:
		return NDET
	}
	return NDET
}

func parseNewNode(site *ast.CallExpr, v *IceTVisitor) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "CreateNewNode" {
			proc := getValue(site.Args[0], v)
			v.currentProgram.AddProc(v.currentProccess)
			if !v.inSet {
				v.currentProcId = proc
			}
			v.currentProccess = icetTerm.NewProcess()
		}
	}
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

func parseForLoop(loopTerm *ast.RangeStmt, v *IceTVisitor) bool {
	domain, ok := loopTerm.X.(*ast.SelectorExpr)
	if ok && domain.Sel.Name == "PeerIds" {
		loopComments := v.Comments.Filter(loopTerm.Body)
		invariant := parseComments(loopComments.Comments(), inv)
		loopVar := loopTerm.Key.(*ast.Ident).Name
		loopVar = strings.ToUpper(loopVar)
		lv := makeNewIceTVisitor(v.Comments)
		lv.currentProcId = v.currentProcId
		lv.inSet = v.inSet
		ast.Walk(lv, loopTerm.Body)
		v.Declarations.Append(&lv.Declarations)
		LoopStmt := icetTerm.ForLoop{ProcID: v.currentProcId, LoopVar: loopVar, Set: v.currentSet, Invariant: invariant, Stmts: *lv.currentProccess}
		v.currentProccess.AddStmt(&LoopStmt)
		return true
	}
	return false
}

func parseAssign(site *ast.CallExpr, v *IceTVisitor) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		// variable.Assign(value)
		if sel.Sel.Name == "Assign" {
			variable := getValue(sel.X, v)
			value := getValue(site.Args[0], v)
			v.currentProccess.AddStmt(&icetTerm.Assign{ProcID: v.currentProcId, Var: variable, Value: value, IsMap: false})
			// _map.Put(key,value)
		} else if sel.Sel.Name == "Put" {
			_map := getValue(sel.X, v)
			key := getValue(site.Args[0], v)
			value := getValue(site.Args[1], v)
			v.currentProccess.AddStmt(&icetTerm.Assign{ProcID: v.currentProcId, Var: _map, Value: value, Key: key, IsMap: true})

		}
	}
}

func parseSend(site *ast.CallExpr, v *IceTVisitor) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "Send" {
			arg1 := getValue(site.Args[0], v)
			arg2 := getValue(site.Args[1], v)
			v.currentProccess.AddStmt(&icetTerm.Send{ProcID: v.currentProcId, RecipientID: arg1, Value: arg2})

		}
		if sel.Sel.Name == "SendPair" {
			arg1 := getValue(site.Args[0], v)
			arg2 := getValue(site.Args[1], v)
			arg3 := getValue(site.Args[2], v)
			pair := fmt.Sprintf("pair(%v,%v)", arg2, arg3)
			v.currentProccess.AddStmt(&icetTerm.Send{ProcID: v.currentProcId, RecipientID: arg1, Value: pair})
		}
	}
}

func parseSymSetDecl(decl *ast.FuncDecl, v *IceTVisitor) bool {
	for _, stmt := range decl.Body.List {
		stmt, ok := stmt.(*ast.ExprStmt)
		if ok {
			stmt, ok := stmt.X.(*ast.CallExpr)
			if ok {
				set, ok := parseStartSymSet(stmt, v)
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

func parseSymAssign(site *ast.CallExpr, v *IceTVisitor) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "AssignSymSet" {
			v.currentSet = getValue(site.Args[0], v)
		}
	}
}

func parseStartSymSet(site *ast.CallExpr, v *IceTVisitor) (*icetTerm.SymSet, bool) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "StartSymSet" {
			procVar := strings.ToUpper(getValue(site.Args[1], v))
			setName := getValue(site.Args[0], v)
			set := icetTerm.SymSet{ProcVar: procVar, Name: setName, Stmts: *icetTerm.NewProcess()}
			return &set, true
		}
	}
	return nil, false
}

func parseDeclaration(assign *ast.AssignStmt, v *IceTVisitor) {
	if len(assign.Rhs) == 1 {
		site, ok := assign.Rhs[0].(*ast.CallExpr)
		if ok {
			sel, ok := site.Fun.(*ast.SelectorExpr)
			if ok {
				varName := getValue(assign.Lhs[0], v)
				var varType = "unknown"
				ok := false
				// switch variable type
				if sel.Sel.Name == "NewVar" {
					varType = "int"
					ok = true
				} else if sel.Sel.Name == "NewMap" {
					varType = "map(int, int)"
					ok = true
				}
				// if found, add assignment
				if ok {
					if v.inSet {
						decl := fmt.Sprintf("decl(%v, map(set(%v), %v))", varName, v.currentSet, varType)
						v.Declarations.Decls = append(v.Declarations.Decls, decl)
					} else {
						decl := fmt.Sprintf("decl(%v, %v)", varName, varType)
						v.Declarations.Decls = append(v.Declarations.Decls, decl)
					}
				}
			}
		}
	}
}

func parseRecv(assign *ast.AssignStmt, v *IceTVisitor) {
	if len(assign.Rhs) == 1 {
		site, ok := assign.Rhs[0].(*ast.CallExpr)
		if ok {
			sel, ok := site.Fun.(*ast.SelectorExpr)
			if ok {
				arg1 := getValue(assign.Lhs[0], v)
				if sel.Sel.Name == "Recv" {
					v.currentProccess.AddStmt(&icetTerm.Recv{ProcID: v.currentProcId, Variable: arg1, IsRecvFrom: false})
				}
				if sel.Sel.Name == "RecvFrom" {
					id := getValue(site.Args[0], v)
					v.currentProccess.AddStmt(&icetTerm.Recv{ProcID: v.currentProcId, Variable: arg1, FromId: id, IsRecvFrom: true})
				}
				if sel.Sel.Name == "RecvPair" {
					l := getValue(assign.Lhs[0], v)
					r := getValue(assign.Lhs[1], v)
					pair := fmt.Sprintf("pair(%v,%v)", l, r)
					v.Declarations.AppendDecl(fmt.Sprintf("decl(%v,int)", l))
					v.Declarations.AppendDecl(fmt.Sprintf("decl(%v,int)", r))
					v.currentProccess.AddStmt(&icetTerm.Recv{ProcID: v.currentProcId, Variable: pair, IsRecvFrom: false})
				}
				if sel.Sel.Name == "RecvPairFrom" {
					l := getValue(assign.Lhs[0], v)
					r := getValue(assign.Lhs[1], v)
					pair := fmt.Sprintf("pair(%v,%v)", l, r)
					id := getValue(site.Args[0], v)
					v.Declarations.AppendDecl(fmt.Sprintf("decl(%v,int)", l))
					v.Declarations.AppendDecl(fmt.Sprintf("decl(%v,int)", r))
					v.currentProccess.AddStmt(&icetTerm.Recv{ProcID: v.currentProcId, Variable: pair, FromId: id, IsRecvFrom: true})
				}
			}
		}
	}
}

// parsing conditionals
func parseConditional(ifStmt *ast.IfStmt, v *IceTVisitor) bool {
	//parse condition
	var vr *IceTVisitor
	cond := parseCondition(ifStmt.Cond, v)
	// parse left subexpression
	vl := makeNewIceTVisitor(v.Comments)
	vl.currentProcId = v.currentProcId
	vl.inSet = v.inSet
	ast.Walk(vl, ifStmt.Body)
	// parse right subexpression
	var rightproc *icetTerm.Process
	if ifStmt.Else != nil {
		vr = makeNewIceTVisitor(v.Comments)
		vr.currentProcId = v.currentProcId
		vr.inSet = v.inSet
		ast.Walk(vr, ifStmt.Else)
		rightproc = vr.currentProccess
	} else {
		rightproc = icetTerm.NewProcess()
	}
	if !vl.currentProccess.IsEmpty() {
		ifStmt := &icetTerm.Conditional{ProcID: v.currentProcId, Cond: cond, Left: *vl.currentProccess, Right: *rightproc}
		v.currentProccess.AddStmt(ifStmt)
		v.Declarations.Append(&vl.Declarations)
		if vr != nil {
			v.Declarations.Append(&vr.Declarations)
		}
		return true
	}
	return false
}

func parseCondition(cond ast.Expr, v *IceTVisitor) string {
	switch cond.(type) {
	case *ast.BinaryExpr:
		binExp := cond.(*ast.BinaryExpr)
		left := parseCondition(binExp.X, v)
		right := parseCondition(binExp.Y, v)
		// equality
		if binExp.Op.String() == "==" {
			return fmt.Sprintf("%v=%v", left, right)
		}
		// and
		if binExp.Op.String() == "&&" {
			return fmt.Sprintf("and([%v,%v])", left, right)
		}
		// or
		if binExp.Op.String() == "||" {
			return fmt.Sprintf("or([%v,%v])", left, right)
		}
		return fmt.Sprintf("%v%v%v", left, binExp.Op.String(), right)
	case *ast.ParenExpr:
		parenExp := cond.(*ast.ParenExpr)
		exp := parseCondition(parenExp.X, v)
		return fmt.Sprintf("(%v)", exp)
	default:
		val := getValue(cond, v)
		if v.inSet && isIdentifier(val) {
			val = fmt.Sprintf("ref(%v,%v)", val, v.currentProcId)
		}
		return val
	}
}

// helper functions for parsing

func isIdentifier(s string) bool {
	if s == NDET {
		return false
	}
	for _, c := range s {
		if !unicode.IsLetter(c) {
			return false
		}
	}
	return true
}

func isInt(s string) bool {
	for _, c := range s {
		if !unicode.IsDigit(c) {
			return false
		}
	}
	return true
}
