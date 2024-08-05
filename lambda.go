package main

import (
	"bufio"
	"fmt"
	"io"
	"log"
	"os"
	"strconv"
	"unicode"
)

const (
	Lambda int = iota
	LParen
	RParen
	Dot
	Equals
	Ident

	LamTerm
	VarTerm
	AppTerm
	LetTerm
)

var (
	environment map[string]Term = make(map[string]Term)
	verbose                     = false
	natural                     = false

	prelude = []string{
		"I = λa.a",
		"M = λf.f f",
		"K = λa.λb.a",
		"KI = K I",
		"C = λf.λa.λb.f b a",
		"B = λf.λg.λa.f(g a)",
		"B1 = B B B",
		"Th = λa.λf.f a",
		"V = λa.λb.λf.f a b",
		"S = λa.λb.λc.a c (b c)",

		"T = K",
		"F = KI",
		"and = λa.λb.a b a",
		"or = λa.λb.a a b",
		"eq = λa.λb.a (b T F) (b F T)",
		"not = C",

		"pair = V",
		"fst = λp.p K",
		"snd = λp.p KI",
		"phi = λp.pair (snd p) (succ (snd p))",

		"succ = λn.λf.B f (n f)",
		"pred = λn.fst (n phi (pair 0 0))",
		"plus = λa.λb.a succ b",
		"sub  = λn.λk.k pred n",
		"mult = B",
		"pow = Th",
		"is0 = λa.a (K F) T",
		"leq = λn.λk.is0 (sub n k)",
		"gt = B1 not leq",
		"eq_num = λn.λk.and (leq n k) (leq k n)",
		"lt = λa.λb.and(leq a b)((B1 not eq_num)a b)",
		"geq = B1 not lt",
	}
)

type Token struct {
	ttype int
	value string
}

type Parser struct {
	toks []Token
}

type FreeVarList struct {
	fvs map[string]struct{}
}

type Term interface {
	etype() int
	printTerm(indent int)
	PPrint()
	execute() Term
	freeVars(vars *FreeVarList)
	rename(name string, to_name string) Term
	betaReduce(name string, arg Term) Term
	equal(other Term) bool
}

type Abstraction struct {
	arg  string
	expr Term
}

type Var struct {
	name string
}

type Application struct {
	toCall Term
	arg    Term
}

type Let struct {
	name string
	expr Term
}

func newFreeVarList() FreeVarList {
	return FreeVarList{make(map[string]struct{})}
}

func (vars *FreeVarList) add(name string) {
	vars.fvs[name] = struct{}{}
}

func (vars *FreeVarList) contains(name string) bool {
	_, ok := vars.fvs[name]
	if ok {
		return true
	}
	return false
}

func (vars *FreeVarList) toList() []string {
	ret := make([]string, len(vars.fvs)+1)
	i := 0
	for k := range vars.fvs {
		ret[i] = k
		i++
	}
	return ret
}

func (Abstraction) etype() int {
	return LamTerm
}

func (Var) etype() int {
	return VarTerm
}

func (Application) etype() int {
	return AppTerm
}

func (Let) etype() int {
	return LetTerm
}

func (f Abstraction) printTerm(indent int) {
	for i := 0; i < indent; i++ {
		fmt.Print("  ")
	}
	fmt.Print("FUNCTION - Argument: ")
	fmt.Print(f.arg)
	fmt.Print("\n")
	f.expr.printTerm(indent + 1)
}

func (f Abstraction) PPrint() {
	fmt.Print("\u03bb")
	fmt.Print(f.arg)
	fmt.Print(".")
	f.expr.PPrint()
}

func (v Var) printTerm(indent int) {
	for i := 0; i < indent; i++ {
		fmt.Print("  ")
	}
	fmt.Print("VARIABLE ")
	fmt.Print(v.name)
	fmt.Print("\n")
}

func (v Var) PPrint() {
	fmt.Print(v.name)
}

func (c Application) printTerm(indent int) {
	for i := 0; i < indent; i++ {
		fmt.Print("  ")
	}
	fmt.Println("APPLICATION")
	c.toCall.printTerm(indent + 1)
	for i := 0; i < indent+1; i++ {
		fmt.Print("  ")
	}
	fmt.Println("With Argument")
	c.arg.printTerm(indent + 2)
}

func (c Application) PPrint() {
	fmt.Print("(")
	c.toCall.PPrint()
	fmt.Print(" ")
	c.arg.PPrint()
	fmt.Print(")")
}

func (a Let) printTerm(indent int) {
	for i := 0; i < indent; i++ {
		fmt.Print("  ")
	}
	fmt.Print("LET: ")
	fmt.Print(a.name)
	fmt.Print("\n")
	a.expr.printTerm(indent + 1)
}

func (Let) PPrint() {
	fmt.Print("")
}

func (a Abstraction) equal(other Term) bool {
	if other.etype() != LamTerm {
		return false
	}
	otherA := other.(*Abstraction)
	if a.arg == otherA.arg {
		return a.expr.equal(otherA.expr)
	}
	fvs := newFreeVarList()
	otherA.expr.freeVars(&fvs)
	if !fvs.contains(a.arg) {
		return a.expr.equal(otherA.expr.rename(otherA.arg, a.arg))
	}
	a.expr.freeVars(&fvs)
	fvs_list := fvs.toList()
	fvs_list = append(fvs_list, otherA.arg)
	arg_p := newName(a.arg, fvs_list)
	return a.expr.rename(a.arg, arg_p).equal(otherA.expr.rename(otherA.arg, arg_p))
}

func (v Var) equal(other Term) bool {
	if other.etype() != VarTerm {
		return false
	}
	otherV := other.(*Var)
	return v.name == otherV.name
}

func (a Application) equal(other Term) bool {
	if other.etype() != AppTerm {
		return false
	}
	otherA := other.(*Application)
	return a.toCall.equal(otherA.toCall) &&
		a.arg.equal(otherA.arg)
}

func (Let) equal(other Term) bool {
	return false
}

func newName(name string, names []string) string {
	i := 0
	for {
		if verbose {
			log.Println("New name of ", name, " from ", names, " i = ", i)
		}
		nname := name + strconv.Itoa(i)
		found := false
		for _, n := range names {
			if nname == n {
				found = true
				break
			}
		}
		if !found {
			return nname
		}
		i++
	}
}

func (f Abstraction) execute() Term {
	if verbose {
		log.Println("Execute Abstraction")
	}
	return &f
}

func (f Abstraction) freeVars(vars *FreeVarList) {
	if verbose {
		log.Println("Calculate FreeVars for Abstraction ", (*vars).fvs)
	}
	vars.add(f.arg)
	f.expr.freeVars(vars)
}

func (f Abstraction) rename(name string, to_name string) Term {
	if verbose {
		log.Println("Abstraction rename ", name, " to ", to_name)
	}
	if f.arg == name {
		return &f
	}
	return &Abstraction{f.arg, f.expr.rename(name, to_name)}
}

func (f Abstraction) betaReduce(name string, arg Term) Term {
	if verbose {
		log.Println("Beta Reduce Abstraction ", name)
	}
	if f.arg == name {
		return &f
	}
	fvs := newFreeVarList()
	arg.freeVars(&fvs)
	if !fvs.contains(f.arg) {
		return &Abstraction{f.arg, f.expr.betaReduce(name, arg)}
	}
	f.expr.freeVars(&fvs)
	fvs_list := fvs.toList()
	fvs_list = append(fvs_list, name)
	arg_p := newName(f.arg, fvs_list)
	return &Abstraction{arg_p, f.expr.rename(f.arg, arg_p).betaReduce(name, arg)}
}

func numToAbstraction(n uint64) Term {
	var expr Term
	expr = &Var{"b"}
	for i := uint64(0); i < n; i++ {
		expr = &Application{&Var{"a"}, expr}
	}
	return &Abstraction{"a", &Abstraction{"b", expr}}
}

func (v Var) execute() Term {
	if verbose {
		log.Println("Execute Var ", v.name)
	}
	val, ok := environment[v.name]
	if ok {
		return val.execute()
	}
	if natural {
		n, err := strconv.ParseUint(v.name, 10, 0)
		if err == nil {
			return numToAbstraction(n)
		}
	}
	return &v
}

func (v Var) freeVars(vars *FreeVarList) {
	if verbose {
		log.Println("Calculate FreeVars ", (*vars).fvs, " for var ", v.name)
	}
	if vars.contains(v.name) {
		return
	}
	x, ok := environment[v.name]
	if ok {
		x.freeVars(vars)
		return
	}
	vars.add(v.name)
}

func (v Var) rename(name string, to_name string) Term {
	if verbose {
		log.Println("Rename Var ", name, " to ", to_name)
	}
	if v.name == name {
		return &Var{to_name}
	}
	return &v
}

func (v Var) betaReduce(name string, arg Term) Term {
	if verbose {
		log.Println("Beta Reduce Var ", v.name)
	}
	if v.name == name {
		return arg
	}
	return &v
}

func (c Application) execute() Term {
	if verbose {
		log.Println("Execute Application")
	}
	toCall := c.toCall.execute()
	if toCall.etype() == LamTerm {
		lambda := toCall.(*Abstraction)
		return lambda.expr.betaReduce(lambda.arg, c.arg).execute()
	}
	return &c
}

func (c Application) freeVars(vars *FreeVarList) {
	if verbose {
		log.Println("Calculate Application FreeVars ", (*vars).fvs)
	}
	c.toCall.freeVars(vars)
	c.arg.freeVars(vars)
}

func (c Application) rename(name string, to_name string) Term {
	if verbose {
		log.Println("Rename Application ", name, " to ", to_name)
	}
	return &Application{c.toCall.rename(name, to_name),
		c.arg.rename(name, to_name)}
}

func (c Application) betaReduce(name string, arg Term) Term {
	if verbose {
		log.Println("Beta Reduce Application ", name)
	}
	return &Application{c.toCall.betaReduce(name, arg),
		c.arg.betaReduce(name, arg)}
}

func (a Let) execute() Term {
	environment[a.name] = a.expr
	return environment[a.name]
}

func (Let) freeVars(vars *FreeVarList) {

}

func (Let) rename(name string, to_name string) Term {
	return nil
}

func (Let) betaReduce(name string, value Term) Term {
	return nil
}

func norm(term Term, c int) Term {
	if c >= 10000 {
		return term
	}
	switch t := term.execute().(type) {
	case *Abstraction:
		return &Abstraction{t.arg, norm(t.expr, c+1)}
	case *Var:
		return t
	case *Application:
		return &Application{norm(t.toCall, c+1), norm(t.arg, c+1)}
	case *Let:
		return t
	}
	return nil
}

func PrintToken(tok Token) {
	switch tok.ttype {
	case Lambda:
		fmt.Print("\u03bb")
	case LParen:
		fmt.Print("LPAREN")
	case RParen:
		fmt.Print("RPAREN")
	case Dot:
		fmt.Print("DOT")
	case Equals:
		fmt.Print("EQUALS")
	case Ident:
		fmt.Print("[IDENT ")
		fmt.Print(tok.value)
		fmt.Print("]")
	}
}

func PrintTokens(toks []Token) {
	for i, tok := range toks {
		if i > 0 {
			fmt.Print(" ")
		}
		PrintToken(tok)
	}
	fmt.Println("")
}

func (parser *Parser) parseAtom() Term {
	if len(parser.toks) == 0 {
		return nil
	}
	if parser.toks[0].ttype == LParen {
		parser.skip(1)
		term := parser.parseTerm()
		// Should be at RParen now
		parser.skip(1)
		return term
	} else if parser.toks[0].ttype == Ident {
		v := &Var{parser.toks[0].value}
		parser.skip(1)
		return v
	}
	return nil
}

func (parser *Parser) parseApplication() Term {
	if len(parser.toks) == 0 {
		return nil
	}
	lhs := parser.parseAtom()
	for {
		rhs := parser.parseAtom()
		if rhs == nil {
			return lhs
		}
		lhs = &Application{lhs, rhs}
	}
}

func (parser *Parser) parseTerm() Term {
	if len(parser.toks) == 0 {
		return nil
	}
	if parser.toks[0].ttype == Lambda && len(parser.toks) > 3 {
		arg := parser.toks[1].value
		// Should have DOT now
		parser.skip(3)
		term := parser.parseTerm()
		return &Abstraction{arg, term}
	}
	return parser.parseApplication()
}

func (parser *Parser) parse() Term {
	if len(parser.toks) >= 2 && parser.toks[0].ttype == Ident &&
		parser.toks[1].ttype == Equals {
		to_bind := parser.toks[0].value
		parser.skip(2)
		expr := parser.parseTerm()
		return &Let{name: to_bind, expr: expr}
	}
	expr := parser.parseTerm()
	return expr
}

func (parser *Parser) skip(i int) {
	parser.toks = parser.toks[i:]
}

func lex(expr string) []Token {
	toks := make([]Token, 0)
	inIdent := false
	ident := make([]rune, 0)
	for _, c := range expr {
		if unicode.IsSpace(c) {
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			continue
		}
		switch c {
		case '(':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{LParen, string(c)})
		case ')':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{RParen, string(c)})
		case '.':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{Dot, string(c)})
		case '\\':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{Lambda, string(c)})
		case '\u03bb':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{Lambda, string(c)})
		case '=':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{Equals, string(c)})
		default:
			inIdent = true
			ident = append(ident, c)
		}
	}
	if inIdent {
		toks = append(toks, Token{Ident, string(ident)})
	}
	return toks
}

func isNatural(lam *Abstraction) bool {
	if lam.expr.etype() != LamTerm {
		return false
	}
	firstName := lam.arg
	sec := lam.expr.(*Abstraction)
	secondName := sec.arg
	if sec.expr.etype() == VarTerm {
		return secondName == sec.expr.(*Var).name
	}
	if sec.expr.etype() != AppTerm {
		return false
	}

	app := sec.expr.(*Application)
	if app.toCall.etype() != VarTerm || app.toCall.(*Var).name != firstName {
		return false
	}
	appP := app.arg
	if appP.etype() == AppTerm {
		app = appP.(*Application)
		for app.toCall.etype() == VarTerm && app.arg.etype() == AppTerm {
			app = app.arg.(*Application)
		}
	}
	return app.toCall.etype() == VarTerm && app.arg.etype() == VarTerm
}

func toNatural(lam *Abstraction) int {
	expr := lam.expr.(*Abstraction).expr
	if expr.etype() == VarTerm {
		return 0
	}
	app := expr.(*Application)
	ret := 1
	for app.arg.etype() == AppTerm {
		ret += 1
		app = app.arg.(*Application)
	}
	return ret
}

func repl() {
	for {
		reader := bufio.NewReader(os.Stdin)
		fmt.Print("> ")
		text, err := reader.ReadString('\n')
		if err != nil {
			if err != io.EOF {
				fmt.Println("Error")
			}
			break
		}
		if len(text) == 1 {
			continue
		}
		toks := lex(text)
		//PrintTokens(toks)
		parser := Parser{toks}
		expr := parser.parse()
		//expr.printTerm(0)
		f := norm(expr, 0)
		if natural && f.etype() == LamTerm && isNatural(f.(*Abstraction)) {
			fmt.Print(toNatural(f.(*Abstraction)))
			fmt.Print(" (")
			f.PPrint()
			fmt.Print(")")
		} else if f.etype() == LamTerm {
			for n, e := range environment {
				if f.equal(norm(e, 0)) {
					fmt.Print(n, " ")
				}
			}
			fmt.Print("(")
			f.PPrint()
			fmt.Print(")")
		} else {
			f.PPrint()
		}
		fmt.Println("")
	}
}

func loadFile(name string) {
	file, err := os.Open(name)
	if err != nil {
		log.Fatal(err)
	}
	defer file.Close()

	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		if len(scanner.Text()) == 0 {
			continue
		}
		parser := Parser{lex(scanner.Text())}
		expr := parser.parse()
		norm(expr, 0)
	}

	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

func main() {
	for args := os.Args[1:]; len(args) > 0; args = args[1:] {
		if args[0] == "--prelude" {
			for _, l := range prelude {
				parser := Parser{lex(l)}
				norm(parser.parse(), 0)
			}
			natural = true
		} else if args[0] == "--load" && len(args) > 1 {
			log.Println("Opening ", args[1])
			loadFile(args[1])
			args = args[1:]
		}
	}
	repl()
}
