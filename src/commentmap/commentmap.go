package commentmap

import (
	"go/ast"
	"go/token"
)

type RelPos int

const (
	Before RelPos = iota
	After         = iota
)

type Comment struct {
	Comment string
	Pos     RelPos
}

type Position struct {
	Start token.Pos
	End   token.Pos
}

type CMapVisitor struct {
	Node2Comment map[ast.Node][]Comment
	CmtStr2Node  map[string]ast.Node
	CmtStr2Pos   map[string]*Position
	Comments     ast.CommentMap
}

func MakeCMapVisitor(comments ast.CommentMap) *CMapVisitor {
	// Mapping nodes to comments s.t. each comment is associated with at most one node.
	v := &CMapVisitor{
		make(map[ast.Node][]Comment),
		make(map[string]ast.Node),
		make(map[string]*Position),
		comments}
	return v
}

func (v *CMapVisitor) Visit(node ast.Node) (w ast.Visitor) {
	// map each comment to the most specific node it is associated with
	if node != nil {
		comments := v.Comments.Filter(node)
		for _, c := range comments.Comments() {
			comment := c.Text()
			oldNode, exists := v.CmtStr2Node[comment]
			if !exists || isSubnode(node, oldNode) {
				v.CmtStr2Node[comment] = node
				v.CmtStr2Pos[comment] = &Position{c.Pos(), c.End()}
			}
		}
	}
	return v
}

func isSubnode(n ast.Node, m ast.Node) bool {
	return n.Pos() >= m.Pos() && n.End() <= m.End()
}

func (v *CMapVisitor) getRelativePosition(comment string, node ast.Node) RelPos {
	var relPos RelPos
	pos := v.CmtStr2Pos[comment]
	if pos.Start <= node.Pos() {
		relPos = Before
	} else if pos.End >= node.End() {
		relPos = After
	}
	return relPos
}

func (v *CMapVisitor) MapComments() {
	for comment, node := range v.CmtStr2Node {
		comments, exists := v.Node2Comment[node]
		if !exists {
			comments = make([]Comment, 0)
		}
		relPos := v.getRelativePosition(comment, node)
		comments = append(comments, Comment{Comment: comment, Pos: relPos})
		v.Node2Comment[node] = comments
	}
}
