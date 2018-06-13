package icet

import (
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"icetTerm"
	"icetcustom"
	"log"
	"strings"
	"unicode"
)

const COMMENT_SIZE = 5
const ANNOTATION_START = "{-@"
const ANNOTATION_END = "-@}"
const INVARIANT_PREFIX = "invariant:"
const PROPERTY_PREFIX = "ensures:"
const PRECONDITION_PREFIX = "pre:"
const ASSUMPION_PREFIX = "assume:"
const DECLARATION_PREFIX = "declare:"
const NDET = "ndet"

var AnnotTypes = []icetTerm.AnnotatationType{icetTerm.Pre, icetTerm.Assume}
var PropertyTypes = []icetTerm.AnnotatationType{icetTerm.Prop}
var InvariantTypes = []icetTerm.AnnotatationType{icetTerm.Inv}
var DeclarationTypes = []icetTerm.AnnotatationType{icetTerm.Declare}

type IceTVisitor struct {
	CurrentProcId    string
	currentProgram   *icetTerm.Program
	currentProccess  *icetTerm.Process
	currentSet       string
	currentPeerSet   string
	currentPeerID    string
	CurrentIDType    icetTerm.IDType
	currentSwitchTag string
	inSet            bool
	IceTTerm         string
	Comments         ast.CommentMap
	Property         string
	Declarations     icetTerm.Declarations
	fileSet          *token.FileSet
	isGhostVar       map[string]bool
	constMap         map[string]string
	//parses custom sends and receives
	Parser icetcustom.CustomParser
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

func MakeNewIceTVisitor() *IceTVisitor {
	v := &IceTVisitor{"",
		icetTerm.NewProgram(),
		icetTerm.NewProcess(),
		"",
		"",
		"",
		icetTerm.Pid,
		"",
		false,
		"",
		nil,
		"",
		icetTerm.Declarations{Decls: make([]string, 0)},
		nil,
		make(map[string]bool),
		make(map[string]string),
		&icetcustom.DefaultParser{}}
	return v
}

func main() {
	// parsing file
	flag.Parse()
	if flag.NArg() != 1 {
		log.Fatal("usage: icet <go file>")
	}
	file := flag.Args()[0]
	v := MakeNewIceTVisitor()
	term := v.ExtractIcetTerm(file)
	fmt.Printf("%v.", term)
}

func (v *IceTVisitor) ExtractIcetTerm(file string) string {
	fset := token.NewFileSet()
	node, err := parser.ParseFile(fset, file, nil, parser.ParseComments)
	v.Comments = ast.NewCommentMap(fset, node, node.Comments)
	v.fileSet = fset
	if err != nil {
		log.Fatal(err)
	}
	propertySet := parseComments(v.Comments.Comments(), v.CurrentProcId, PropertyTypes)
	v.Property = propertySet.PrintIceT()
	addDeclarations(v, v.Comments.Comments())
	ast.Walk(v, node)
	return v.MakeIceTTerm()
}

func (v *IceTVisitor) Visit(node ast.Node) (w ast.Visitor) {

	switch node.(type) {

	case *ast.ExprStmt:
		parseAssign(node.(*ast.ExprStmt), v)

	case *ast.CallExpr:
		parseSend(node.(*ast.CallExpr), v)
		parseNewNode(node.(*ast.CallExpr), v)
		parseSymAssign(node.(*ast.CallExpr), v)

	case *ast.AssignStmt:
		parseRecv(node.(*ast.AssignStmt), v)
		parseDeclaration(node.(*ast.AssignStmt), v)

	case *ast.RangeStmt:
		ok := parseForLoop(node.(*ast.RangeStmt), v)
		if ok {
			return nil // children were already traversed
		}

	case *ast.GenDecl:
		parseConstant(node.(*ast.GenDecl), v)

	case *ast.IfStmt:
		ok := parseConditional(node.(*ast.IfStmt), v)
		if ok {
			return nil
		}

	case *ast.SwitchStmt:
		ok := parseSwitchStmt(node.(*ast.SwitchStmt), v)
		if ok {
			return nil
		}

	case *ast.CaseClause:
		parseCaseClause(node.(*ast.CaseClause), v)
		return nil

	case *ast.ForStmt:
		parseRepeat(node.(*ast.ForStmt), v)
		return nil

	case *ast.FuncDecl:
		ok := parseSymSetDecl(node.(*ast.FuncDecl), v)
		if ok {
			return nil
		}
	}
	return v
}

func getLineNumber(v *IceTVisitor, pos token.Pos) int {
	file := v.fileSet.File(pos)
	return file.Position(pos).Line
}

func (v *IceTVisitor) GetValue(stmt ast.Node) string {
	v.CurrentIDType = icetTerm.Pid
	switch stmt.(type) {
	case *ast.BasicLit:
		return stringRemoveQuotes(stmt.(*ast.BasicLit).Value)
	case *ast.Ident:
		name := stmt.(*ast.Ident).Name
		value, ok := v.constMap[name]
		if ok {
			return value
		}
		return stringRemoveQuotes(name)
	case *ast.CallExpr:
		site := stmt.(*ast.CallExpr)
		switch site.Fun.(type) {
		case *ast.SelectorExpr:
			sel := site.Fun.(*ast.SelectorExpr)
			if sel.Sel.Name == "Get" {
				v.CurrentIDType = icetTerm.Variable
				return sel.X.(*ast.Ident).Name
			}
			if sel.Sel.Name == "MyId" {
				return v.CurrentProcId
			}
			if sel.Sel.Name == "NumPeers" {
				return fmt.Sprintf("card(%v)", v.currentPeerSet)
			}
		case *ast.Ident:
			ident := site.Fun.(*ast.Ident)
			if ident.Name == "int" || ident.Name == "int32" || ident.Name == "uint8" {
				return v.GetValue(site.Args[0])
			}
			return ident.Name

		default:
			return NDET
		}

	case *ast.BinaryExpr:
		binExp := stmt.(*ast.BinaryExpr)
		e1 := v.GetValue(binExp.X)
		e2 := v.GetValue(binExp.Y)
		return fmt.Sprintf("%v %v %v", e1, binExp.Op.String(), e2)

	default:
		return NDET
	}
	return NDET
}

func addDeclarations(v *IceTVisitor, comments []*ast.CommentGroup) {
	for _, comment := range comments {
		decl, atype := parseComment(comment)
		if atype == icetTerm.Declare {
			v.Declarations.AppendDecl(decl)
		}
	}
}

func parseAnnotations(stmt ast.Node, v *IceTVisitor) {
	if stmt != nil {
		comments := v.Comments.Filter(stmt)
		annots := parseComments(comments.Comments(), v.CurrentProcId, AnnotTypes)
		if len(annots.Annots) > 0 {
			v.currentProccess.AddStmt(annots)
		}
	}
}

func parseNewNode(site *ast.CallExpr, v *IceTVisitor) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "CreateNewNode" {
			proc := v.GetValue(site.Args[0])
			v.currentProgram.AddProc(v.currentProccess)
			if !v.inSet {
				v.CurrentProcId = proc
			}
			v.currentProccess = icetTerm.NewProcess()
		}
	}
}

func parseConstant(decl *ast.GenDecl, v *IceTVisitor) {
	if decl.Tok == token.CONST {
		for _, spec := range decl.Specs {
			valSpec, ok := spec.(*ast.ValueSpec)
			if ok {
				constant := v.GetValue(valSpec.Names[0])
				value := v.GetValue(valSpec.Values[0])
				v.constMap[constant] = value
			}
		}
	}
}

func parseComment(comment *ast.CommentGroup) (string, icetTerm.AnnotatationType) {
	s := comment.Text()
	s = strings.Trim(s, "\n")
	if strings.HasPrefix(s, ANNOTATION_START) && strings.HasSuffix(s, ANNOTATION_END) {
		s = strings.TrimPrefix(s, ANNOTATION_START)
		s = strings.TrimSuffix(s, ANNOTATION_END)
		s = strings.TrimSpace(s)
		if strings.HasPrefix(s, INVARIANT_PREFIX) {
			s = strings.TrimPrefix(s, INVARIANT_PREFIX)
			return s, icetTerm.Inv
		}
		if strings.HasPrefix(s, PROPERTY_PREFIX) {
			s = strings.TrimPrefix(s, PROPERTY_PREFIX)
			return s, icetTerm.Prop
		}
		if strings.HasPrefix(s, PRECONDITION_PREFIX) {
			s = strings.TrimPrefix(s, PRECONDITION_PREFIX)
			return s, icetTerm.Pre
		}
		if strings.HasPrefix(s, ASSUMPION_PREFIX) {
			s = strings.TrimPrefix(s, ASSUMPION_PREFIX)
			return s, icetTerm.Assume
		}
		if strings.HasPrefix(s, DECLARATION_PREFIX) {
			s = strings.TrimPrefix(s, DECLARATION_PREFIX)
			return s, icetTerm.Declare
		}
	}
	return "", icetTerm.None
}

func parseComments(comments []*ast.CommentGroup, procId string, annotTypes []icetTerm.AnnotatationType) *icetTerm.AnnotationSet {
	annotations := icetTerm.NewAnnotationSet()
	for _, comment := range comments {
		annot, atype := parseComment(comment)
		if containsType(atype, annotTypes) {
			annotations.Add(icetTerm.Annotation{Annot: annot, Type: atype, ProcID: procId})
		}
	}
	return annotations
}

func parseForLoop(loopTerm *ast.RangeStmt, v *IceTVisitor) bool {
	domain, ok := loopTerm.X.(*ast.SelectorExpr)
	if ok && domain.Sel.Name == "PeerIds" {
		loopComments := v.Comments.Filter(loopTerm.Body)
		invariantSet := parseComments(loopComments.Comments(), v.CurrentProcId, InvariantTypes)
		invariant := invariantSet.PrintIceT()
		lv := copyVisitor(v)
		lv.currentPeerID = v.GetValue(loopTerm.Key)
		ast.Walk(lv, loopTerm.Body)
		v.Declarations.Append(&lv.Declarations)
		LoopStmt := icetTerm.ForLoop{ProcID: v.CurrentProcId, LoopVar: lv.currentPeerID, Set: v.currentPeerSet, Invariant: invariant, Stmts: *lv.currentProccess}
		v.currentProccess.AddStmt(&LoopStmt)
		return true
	}
	return false
}

func parseRepeat(repeatTerm *ast.ForStmt, v *IceTVisitor) {
	lv := copyVisitor(v)
	ast.Walk(lv, repeatTerm.Body)
	v.Declarations.Append(&lv.Declarations)
	LoopStmt := icetTerm.RepeatLoop{ProcID: v.CurrentProcId, Stmts: *lv.currentProccess}
	v.currentProccess.AddStmt(&LoopStmt)
}

func copyVisitor(v *IceTVisitor) *IceTVisitor {
	cp := MakeNewIceTVisitor()
	cp.CurrentProcId = v.CurrentProcId
	cp.inSet = v.inSet
	cp.fileSet = v.fileSet
	cp.Comments = v.Comments
	cp.currentSwitchTag = v.currentSwitchTag
	cp.currentSet = v.currentSet
	cp.currentPeerSet = v.currentPeerSet
	cp.isGhostVar = v.isGhostVar
	cp.constMap = v.constMap
	cp.Parser = v.Parser
	return cp
}

func parseAssign(expr *ast.ExprStmt, v *IceTVisitor) bool {
	site, ok := expr.X.(*ast.CallExpr)
	if ok {
		sel, ok := site.Fun.(*ast.SelectorExpr)
		if ok {
			// variable.Assign(value)
			if sel.Sel.Name == "Assign" {
				parseAnnotations(expr, v)
				variable := v.GetValue(sel.X)
				value := parseExpression(site.Args[0], v)
				v.currentProccess.AddStmt(&icetTerm.Assign{ProcID: v.CurrentProcId, Var: variable, Value: value, IsMap: false})
				return true
				// _map.Put(key,value)
			} else if sel.Sel.Name == "Put" {
				parseAnnotations(expr, v)
				_map := v.GetValue(sel.X)
				key := v.GetValue(site.Args[0])
				value := parseExpression(site.Args[1], v)
				v.currentProccess.AddStmt(&icetTerm.Assign{ProcID: v.CurrentProcId, Var: _map, Value: value, Key: key, IsMap: true})
				return true
			}
		}
	}
	return false
}

func parseSend(site *ast.CallExpr, v *IceTVisitor) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "Send" {
			val := v.GetValue(site.Args[1])
			recp := v.GetValue(site.Args[0])
			v.currentProccess.AddStmt(&icetTerm.Send{ProcID: v.CurrentProcId, RecipientID: recp, RecipientType: v.CurrentIDType, Value: val})
		}
		if sel.Sel.Name == "SendPair" {
			l := v.GetValue(site.Args[1])
			r := v.GetValue(site.Args[2])
			recp := v.GetValue(site.Args[0])
			pair := fmt.Sprintf("pair(%v,%v)", l, r)
			v.currentProccess.AddStmt(&icetTerm.Send{ProcID: v.CurrentProcId, RecipientID: recp, Value: pair})
		}
		// custom sends
		ok, stmt := v.Parser.ParseSend(sel.Sel.Name, site.Args, v.CurrentProcId, v.CurrentIDType, v.GetValue)
		if ok {
			v.currentProccess.AddStmt(stmt)
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
					sv := copyVisitor(v) //makeNewIceTVisitor(v.Comments, v.fileSet)
					sv.currentSet = set.Name
					sv.inSet = true
					sv.CurrentProcId = set.ProcVar
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
			v.currentPeerSet = v.GetValue(site.Args[0])
		}
	}
}

func parseStartSymSet(site *ast.CallExpr, v *IceTVisitor) (*icetTerm.SymSet, bool) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "StartSymSet" {
			procVar := strings.ToUpper(v.GetValue(site.Args[1]))
			setName := v.GetValue(site.Args[0])
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
				varName := v.GetValue(assign.Lhs[0])
				var varType = "unknown"
				ok := false
				// switch variable type
				if sel.Sel.Name == "NewVar" || sel.Sel.Name == "NewUInt8" {
					varType = "int"
					ok = true
				} else if sel.Sel.Name == "NewMap" {
					varType = "map(int, int)"
					ok = true
				} else if sel.Sel.Name == "NewGhostVar" {
					v.isGhostVar[varName] = true
					ok = false
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
				arg1 := v.GetValue(assign.Lhs[0])
				if sel.Sel.Name == "Recv" {
					v.currentProccess.AddStmt(&icetTerm.Recv{ProcID: v.CurrentProcId, Variable: arg1, IsRecvFrom: false})
				}
				if sel.Sel.Name == "RecvFrom" {
					id := v.GetValue(site.Args[0])
					v.currentProccess.AddStmt(&icetTerm.Recv{ProcID: v.CurrentProcId, Variable: arg1, FromId: id, IsRecvFrom: true})
				}
				if sel.Sel.Name == "RecvPair" {
					l := v.GetValue(assign.Lhs[0])
					r := v.GetValue(assign.Lhs[1])
					pair := fmt.Sprintf("pair(%v,%v)", l, r)
					if v.inSet {
						v.Declarations.AppendDecl(fmt.Sprintf("decl(%v, map(set(%v), int))", l, v.currentSet))
						v.Declarations.AppendDecl(fmt.Sprintf("decl(%v, map(set(%v), int))", r, v.currentSet))
					} else {
						v.Declarations.AppendDecl(fmt.Sprintf("decl(%v,int)", l))
						v.Declarations.AppendDecl(fmt.Sprintf("decl(%v,int)", r))
					}
					v.currentProccess.AddStmt(&icetTerm.Recv{ProcID: v.CurrentProcId, Variable: pair, IsRecvFrom: false})
				}
				if sel.Sel.Name == "RecvPairFrom" {
					l := v.GetValue(assign.Lhs[0])
					r := v.GetValue(assign.Lhs[1])
					pair := fmt.Sprintf("pair(%v,%v)", l, r)
					id := v.GetValue(site.Args[0])
					v.Declarations.AppendDecl(fmt.Sprintf("decl(%v,int)", l))
					v.Declarations.AppendDecl(fmt.Sprintf("decl(%v,int)", r))
					v.currentProccess.AddStmt(&icetTerm.Recv{ProcID: v.CurrentProcId, Variable: pair, FromId: id, IsRecvFrom: true})
				}
				// custom receives
				ok, stmt := v.Parser.ParseReceive(sel.Sel.Name, assign.Lhs, v.GetValue(site.Args[0]), v.CurrentProcId, v.inSet, v.GetValue)
				if ok {
					v.currentProccess.AddStmt(stmt)
				}
			}
		}
	}
}

// parsing conditionals
func parseConditional(ifStmt *ast.IfStmt, v *IceTVisitor) bool {
	//parse condition
	var vr *IceTVisitor
	cond := parseExpression(ifStmt.Cond, v)
	// parse left subexpression
	vl := copyVisitor(v)
	ast.Walk(vl, ifStmt.Body)
	// parse right subexpression
	var rightproc *icetTerm.Process
	if ifStmt.Else != nil {
		vr := copyVisitor(v)
		ast.Walk(vr, ifStmt.Else)
		rightproc = vr.currentProccess
	} else {
		rightproc = icetTerm.NewProcess()
	}
	if !vl.currentProccess.IsEmpty() {
		parseAnnotations(ifStmt, v)
		ifStmt := &icetTerm.Conditional{ProcID: v.CurrentProcId, Cond: cond, Left: *vl.currentProccess, Right: *rightproc}
		v.currentProccess.AddStmt(ifStmt)
		v.Declarations.Append(&vl.Declarations)
		if vr != nil {
			v.Declarations.Append(&vr.Declarations)
		}
		return true
	}
	return false
}

func parseSwitchStmt(switchStmt *ast.SwitchStmt, v *IceTVisitor) bool {
	vb := copyVisitor(v)
	vb.currentSwitchTag = parseExpression(switchStmt.Tag, v)
	ast.Walk(vb, switchStmt.Body)
	if vb != nil {
		parseAnnotations(switchStmt, v)
		v.currentProccess.AddProc(vb.currentProccess)
		v.Declarations.Append(&vb.Declarations)
		return true
	}
	return false
}

func parseCaseClause(caseClause *ast.CaseClause, v *IceTVisitor) {
	caseExpr := parseExpression(caseClause.List[0], v)
	vc := copyVisitor(v)
	ast.Walk(vc, &ast.BlockStmt{List: caseClause.Body, Lbrace: caseClause.Pos(), Rbrace: caseClause.End()})
	cond := fmt.Sprintf("%v==%v", vc.currentSwitchTag, caseExpr)
	ifStmt := &icetTerm.Conditional{ProcID: v.CurrentProcId, Cond: cond, Left: *vc.currentProccess, Right: *icetTerm.NewProcess()}
	v.currentProccess.AddStmt(ifStmt)
}

func parseExpression(cond ast.Expr, v *IceTVisitor) string {
	switch cond.(type) {
	case *ast.BinaryExpr:
		binExp := cond.(*ast.BinaryExpr)
		left := parseExpression(binExp.X, v)
		right := parseExpression(binExp.Y, v)
		// equality
		if binExp.Op.String() == "==" {
			return fmt.Sprintf("%v=%v", left, right)
		}
		// in-equality
		if binExp.Op.String() == ">=" {
			return fmt.Sprintf("%v=<%v", right, left)
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
		exp := parseExpression(parenExp.X, v)
		return fmt.Sprintf("(%v)", exp)
	default:
		val := v.GetValue(cond)
		if v.inSet && isIdentifier(val) && val != v.CurrentProcId {
			proc := v.CurrentProcId
			// if the variable is a ghost variable shadowing another procs var, use the other proc's id
			ok := v.isGhostVar[val]
			if ok {
				proc = v.currentPeerID
			}
			val = fmt.Sprintf("ref(%v,%v)", val, proc)
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

func containsType(_type icetTerm.AnnotatationType, types []icetTerm.AnnotatationType) bool {
	for _, el := range types {
		if el == _type {
			return true
		}
	}
	return false
}
