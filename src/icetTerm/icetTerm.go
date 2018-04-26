package icetTerm

import (
	"fmt"
)

const PROC_SIZE = 5
const STMT_SIZE = 20
const SKIP = "skip"

type IcetTerm interface {
	PrettyPrint() string
	PrintIceT() string
}

// Programs
type Program struct {
	procs []IcetTerm
}

type Process struct {
	stmts []IcetTerm
}

type Send struct {
	ProcID      string
	RecipientID string
	Value       string
}

type Recv struct {
	ProcID   string
	Variable string
}

type ForLoop struct {
	ProcID    string
	LoopVar   string
	Set       string
	Invariant string
	Stmts     Process
}

type SymSet struct {
	ProcVar string
	Name    string
	Stmts   Process
}

// Send statements
func (s *Send) PrettyPrint() string {
	return fmt.Sprintf("%v: send(%v, %v)", s.ProcID, s.RecipientID, s.Value)
}

func (s *Send) PrintIceT() string {
	return fmt.Sprintf("send(%v, e_pid(%v), %v)", s.ProcID, s.RecipientID, s.Value)
}

// Receive statements
func (r *Recv) PrettyPrint() string {
	return fmt.Sprintf("%v: recv(%v)", r.ProcID, r.Variable)
}

func (r *Recv) PrintIceT() string {
	return fmt.Sprintf("recv(%v, %v)", r.ProcID, r.Variable)
}

// For Loops

func (l *ForLoop) PrettyPrint() string {
	return fmt.Sprintf("invariant: %v\n%v: for %v in %v do %v end", l.Invariant, l.ProcID, l.LoopVar, l.Set, l.Stmts.PrettyPrint())
}

func (l *ForLoop) PrintIceT() string {
	//TODO stub
	return fmt.Sprintf("for(%v, %v, %v, done, %v, %v)", l.ProcID, l.LoopVar, l.Set, l.Invariant, l.Stmts.PrintIceT())
}

func (s *SymSet) PrintIceT() string {
	return fmt.Sprintf("sym(%v, %v, %v)", s.ProcVar, s.Name, s.Stmts.PrintIceT())
}

func (s *SymSet) PrettyPrint() string {
	return fmt.Sprintf("∏_%v:%v(%v)", s.ProcVar, s.Name, s.Stmts.PrettyPrint())
}

// Programs
func NewProgram() *Program {
	return &Program{make([]IcetTerm, 0, PROC_SIZE)}
}

func (p *Program) AddProc(proc IcetTerm) {
	p.procs = append(p.procs, proc)
}

func (p *Program) RemoveLastProc() (IcetTerm, bool) {
	if len(p.procs) > 0 {
		proc := p.procs[len(p.procs)-1]
		p.procs = p.procs[:len(p.procs)-1]
		return proc, true
	}
	return NewProcess(), false
}

func (p *Program) PrettyPrint() string {
	var prog string
	if len(p.procs) > 0 {
		prog = p.procs[0].PrettyPrint()
		for _, proccess := range p.procs[1:] {
			this := proccess.PrettyPrint()
			prog = fmt.Sprintf("%v || %v", prog, this)
		}
	} else {
		prog = SKIP
	}
	return prog
}

func (p *Program) PrintIceT() string {
	var prog string
	if len(p.procs) > 0 {
		prog = fmt.Sprintf("par([%v", p.procs[0].PrintIceT())
		for _, proccess := range p.procs[1:] {
			this := proccess.PrintIceT()
			prog = fmt.Sprintf("%v,%v", prog, this)
		}
		prog = fmt.Sprintf("%v])", prog)
	} else {
		prog = SKIP
	}
	return fmt.Sprintf("prog(prog,[], false, %v)", prog)
}

// Processes
func NewProcess() *Process {
	return &Process{make([]IcetTerm, 0, STMT_SIZE)}
}

func (proc *Process) Len() int {
	return len(proc.stmts)
}

func (proc *Process) AddStmt(stmt IcetTerm) {
	proc.stmts = append(proc.stmts, stmt)
}

func (proc *Process) PrettyPrint() string {
	var stmts string
	if len(proc.stmts) > 0 {
		stmts = proc.stmts[0].PrettyPrint()
		for _, stmt := range proc.stmts[1:] {
			stmts = fmt.Sprintf("%v;%v", stmts, stmt.PrettyPrint())
		}
	} else {
		stmts = SKIP
	}
	return stmts
}

func (proc *Process) PrintIceT() string {
	var stmts string
	if len(proc.stmts) > 0 {
		stmts = fmt.Sprintf("seq([%v", proc.stmts[0].PrintIceT())
		for _, stmt := range proc.stmts[1:] {
			stmts = fmt.Sprintf("%v,%v", stmts, stmt.PrintIceT())
		}
		stmts = fmt.Sprintf("%v])", stmts)
	} else {
		stmts = SKIP
	}
	return stmts
}
