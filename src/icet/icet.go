package main

import "go/token"
import "go/parser"
import "go/ast"
import "fmt"
import "log"

type IceTVisitor struct {
	IceTTerm string
}

func main() {
	walkAst()
}

func makeNewIceTVisitor() *IceTVisitor {
	v := &IceTVisitor{"skip"}
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
	fmt.Printf("Returned IceTTerm: %v\n", v.IceTTerm)
}

func (v *IceTVisitor) Visit(node ast.Node) (w ast.Visitor) {
	switch node.(type) {
	case *ast.CallExpr:
		sendStr, ok := parseSend(node.(*ast.CallExpr))
		if ok {
			v.IceTTerm = fmt.Sprintf("%v;%v", sendStr, v.IceTTerm)
		}
	case *ast.AssignStmt:
		recvString, ok := parseRecv(node.(*ast.AssignStmt))
		if ok {
			v.IceTTerm = fmt.Sprintf("%v;%v", recvString, v.IceTTerm)
		}

	}
	return v
}

//fmt.Sprintf("at %v, %s", e.When, e.What)
func parseSend(site *ast.CallExpr) (string, bool) {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		if sel.Sel.Name == "Send" {
			arg1 := site.Args[0].(*ast.BasicLit).Value
			arg2 := site.Args[1].(*ast.BasicLit).Value
			return fmt.Sprintf("send(%v, %v)", arg1, arg2), true
		}
	}
	return "", false
}

func parseRecv(assign *ast.AssignStmt) (string, bool) {
	if len(assign.Rhs) == 1 {
		site, ok := assign.Rhs[0].(*ast.CallExpr)
		if ok {
			sel, ok := site.Fun.(*ast.SelectorExpr)
			if ok {
				x, ok := sel.X.(*ast.Ident)
				if ok {
					if sel.Sel.Name == "Recv" && x.Name == "gochai" {
						arg1 := assign.Lhs[0].(*ast.Ident).Name
						return fmt.Sprintf("recv(%v)", arg1), true
					}
				}
			}
		}
	}
	return "", false

}
