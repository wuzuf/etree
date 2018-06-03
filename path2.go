// Copyright 2015 Brett Vickers.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package etree

import (
	"errors"
	"reflect"
	"strconv"
	"unicode/utf8"
	"unsafe"
)

var ErrPathSyntax = errors.New("etree: invalid path")

// TODO:
//  Parse escape codes in strings
//  Optimize candidate list code

/*
A Path2 is an object that represents an optimized version of an XPath-like
search string. A path search string is a slash-separated series of "selectors"
allowing traversal through an XML hierarchy. Although etree path strings are
similar to XPath strings, they have a more limited set of selectors and
filtering options. The following selectors and filters are supported by etree
paths:

    .               Select the current element.
    ..              Select the parent of the current element.
    *               Select all child elements of the current element.
    /               Select the root element when used at the start of a path.
    //              Select all descendants of the current element. If used at
                      the start of a path, select all descendants of the root.
    tag             Select all child elements with the given tag.
    [#]             Select the element of the given index (1-based,
                      negative starts from the end).
    [@attrib]       Select all elements with the given attribute.
    [@attrib='val'] Select all elements with the given attribute set to val.
    [tag]           Select all elements with a child element named tag.
    [tag='val']     Select all elements with a child element named tag
                      and text matching val.
    [text()]        Select all elements with non-empty text.
    [text()='val']  Select all elements whose text matches val.

Examples:

Select the bookstore child element of the root element:
    /bookstore

Beginning a search from the root element, select the title elements of all
descendant book elements having a 'category' attribute of 'WEB':
    //book[@category='WEB']/title

Beginning a search from the current element, select the first descendant book
element with a title child containing the text 'Great Expectations':
    .//book[title='Great Expectations'][1]

Beginning a search from the current element, select all children of book
elements with an attribute 'language' set to 'english':
    ./book/*[@language='english']

Beginning a search from the current element, select all children of book
elements containing the text 'special':
    ./book/*[text()='special']

Beginning a search from the current element, select all descendant book
elements whose title element has an attribute 'language' equal to 'french':
    .//book/title[@language='french']/..

*/
type Path2 struct {
	segments []segment2 // take union of segment results
}

// CompilePath2 creates an optimized version of an XPath-like string that
// can be used to query elements in an element tree.
func CompilePath2(path string) (p Path2, err error) {
	var c compiler2

	toks, err := c.tokenizePath(path)
	if err != nil {
		return p, err
	}

	err = c.parsePath(&p, toks)
	if err != nil {
		return Path2{}, err
	}

	return p, nil
}

// MustCompilePath2 creates an optimized version of an XPath-like string that
// can be used to query elements in an element tree.  Panics if an error
// occurs.  Use this function to create Paths when you know the path is
// valid (i.e., if it's hard-coded).
func MustCompilePath2(path string) Path2 {
	p, err := CompilePath2(path)
	if err != nil {
		panic(err)
	}
	return p
}

/*
Tokens:
  /                     sep
  //                    sep_recurse
  [                     lbracket
  ]                     rbracket
  (                     lparen
  )                     rparen
  |                     union
  =                     equal
  :                     colon
  @                     attrib
  .                     self
  ..                    parent
  *                     wildcard
  '[^']*'               string
  "[^"]*'               string
  [a-zA-Z][a-z_A-Z0-9]* identifier
  -?[0-9][0-9]*         number

Grammar:
  <path>          ::= <sep>? (<segment> <sep>)* <segment>?
  <sep>           ::= '/' | '//'
  <segment>       ::= <segmentExpr> ('|' <segmentExpr>)
  <segmentExpr>   ::= <selector> <filterWrapper>* | '(' <segment> ')'
  <selector>      ::= '.' | '..' | '*' | <name>
  <filterWrapper> ::= '[' <filter> ']'
  <filter>        ::= <filterExpr> ('|' <filterExpr>)*
  <filterExpr>    ::= <filterIndex> | <filterAttrib> | <filterChild> | <filterFunc> | '(' <filter> ')'
  <filterIndex>   ::= number
  <filterAttrib>  ::= '@' <name> | '@' <name> '=' string
  <filterChild>   ::= <name> | <name> '=' string
  <filterFunc>    ::= <name> '(' ')' | <name> '(' ')' '=' string
  <name> 		  ::= ident | ident ':' ident
*/

type segment2 struct {
	exprs []segmentExpr2 // apply union of all segment expressions
}

type segmentExpr2 struct {
	sel     selector2
	filters []filter2 // apply filters in sequence
}

type filter2 struct {
	exprs []filterExpr2 // union of all filter expressions
}

type selector2 interface {
	eval(e *Element) candidates
}

type filterExpr2 interface {
	eval(e *Element, in candidates) candidates
}

var rootSegment = segment2{
	exprs: []segmentExpr2{
		segmentExpr2{
			sel: &selectRoot2{},
		},
	},
}

var descendantsSegment = segment2{
	exprs: []segmentExpr2{
		segmentExpr2{
			sel: &selectDescendants2{},
		},
	},
}

// A compiler generates a compiled path from a path string.
type compiler2 struct {
}

func (c *compiler2) parsePath(p *Path2, toks tokens) (err error) {
	// <path> ::= <sep>? (<segment> <sep>)* <segment>?

	// Check for an absolute path.
	switch toks.peekID() {
	case tokSep:
		p.segments = append(p.segments, rootSegment)
		toks = toks.consume(1)
	case tokSepRecurse:
		p.segments = append(p.segments, rootSegment)
		p.segments = append(p.segments, descendantsSegment)
		toks = toks.consume(1)
	case tokEOL:
		return ErrPathSyntax
	}

	// Process remaining segments.
loop:
	for len(toks) > 0 {
		var s segment2
		toks, err = c.parseSegment2(&s, toks)
		if err != nil {
			return err
		}

		p.segments = append(p.segments, s)

		var tok token
		tok, toks = toks.next()
		switch tok.id {
		case tokSep:
			// do nothing
		case tokSepRecurse:
			p.segments = append(p.segments, descendantsSegment)
		case tokEOL:
			break loop
		default:
			return ErrPathSyntax
		}
	}

	return nil
}

func (c *compiler2) parseSegment2(s *segment2, toks tokens) (remain tokens, err error) {
	// <segment> ::= <segmentExpr> ('|' <segmentExpr>)

	// Parse one or more segments.
	for {
		toks, err = c.parseSegmentExpr2(s, toks)
		if err != nil {
			return nil, err
		}

		if toks.peekID() != tokUnion {
			break
		}
		toks = toks.consume(1)
	}

	return toks, nil
}

func (c *compiler2) parseSegmentExpr2(s *segment2, toks tokens) (remain tokens, err error) {
	// <segmentExpr> ::= <selector> <filterWrapper>* | '(' <segment> ')'

	// Check for parentheses.
	if toks.peekID() == tokLParen {
		var ss segment2
		toks, err = c.parseSegment2(&ss, toks.consume(1))
		if err != nil {
			return nil, err
		}

		s.exprs = append(s.exprs, ss.exprs...)

		var tok token
		tok, toks = toks.next()
		if tok.id != tokRParen {
			return nil, ErrPathSyntax
		}
		return toks, nil
	}

	// Parse the selector.
	var e segmentExpr2
	toks, err = c.parseSelector2(&e.sel, toks)
	if err != nil {
		return nil, err
	}

	// Parse zero or more bracket-wrapped filter expressions.
	for {
		if toks.peekID() != tokLBracket {
			break
		}

		var f filter2
		toks, err = c.parseFilter2(&f, toks.consume(1))
		if err != nil {
			return nil, ErrPathSyntax
		}

		var tok token
		tok, toks = toks.next()
		if tok.id != tokRBracket {
			return nil, ErrPathSyntax
		}

		e.filters = append(e.filters, f)
	}

	s.exprs = append(s.exprs, e)
	return toks, nil
}

func (c *compiler2) parseSelector2(s *selector2, toks tokens) (remain tokens, err error) {
	// <selector> ::= '.' | '..' | '*' | <name>

	switch toks.peekID() {
	case tokSelf:
		toks = toks.consume(1)
		*s = &selectSelf2{}
	case tokParent:
		toks = toks.consume(1)
		*s = &selectParent2{}
	case tokChildren:
		toks = toks.consume(1)
		*s = &selectChildren2{}
	case tokIdentifier:
		var sp, name string
		toks, sp, name, err = c.parseName(toks)
		if err != nil {
			return nil, err
		}
		*s = &selectChildrenByTag2{sp, name}
	default:
		return nil, ErrPathSyntax
	}

	return toks, nil
}

func (c *compiler2) parseName(toks tokens) (remain tokens, sp, name string, err error) {
	// <name> ::= identifier | identifier ':' identifier

	var tok token
	tok, toks = toks.next()
	if toks.peekID() == tokColon {
		sp = tok.value.toString()
		tok, toks = toks.consume(1).next()
		if tok.id != tokIdentifier {
			return nil, "", "", ErrPathSyntax
		}
		return toks, sp, tok.value.toString(), nil
	}
	return toks, "", tok.value.toString(), nil
}

func (c *compiler2) parseFilter2(fu *filter2, toks tokens) (remain tokens, err error) {
	// <filter> ::= <filterExpr> ('|' <filterExpr>)*

	// Parse one or more filter expressions.
	for {
		toks, err = c.parseFilterExpr2(fu, toks)
		if err != nil {
			return nil, err
		}

		if toks.peekID() != tokUnion {
			break
		}
		toks = toks.consume(1)
	}

	return toks, nil
}

func (c *compiler2) parseFilterExpr2(f *filter2, toks tokens) (remain tokens, err error) {
	// <filterExpr> ::= number
	//                | '@' ident | '@' ident '=' string
	//                | ident | ident '=' string
	//                | ident '(' ')' | ident '(' ')' '=' string
	//                | '(' <filter> ')'

	switch toks.peekID() {
	case tokLParen:
		// '(' <filter> ')'
		var ff filter2
		toks, err = c.parseFilter2(&ff, toks.consume(1))
		if err != nil {
			return nil, err
		}
		var tok token
		tok, toks = toks.next()
		if tok.id != tokRParen {
			return nil, ErrPathSyntax
		}
		f.exprs = append(f.exprs, ff.exprs...)

	case tokNumber:
		// number
		var tok token
		tok, toks = toks.next()

		index, _ := strconv.Atoi(string(tok.value))
		if index > 0 {
			index--
		}
		f.exprs = append(f.exprs, &filterIndex2{index})

	case tokAt:
		var sp, key string
		toks, sp, key, err = c.parseName(toks.consume(1))
		if err != nil {
			return nil, err
		}

		if toks.peekID() == tokEqual {
			// '@' <name> '=' string
			var tok token
			tok, toks = toks.consume(1).next()
			if tok.id != tokString {
				return nil, ErrPathSyntax
			}
			f.exprs = append(f.exprs, &filterAttribValue2{sp, key, tok.value.toString()})
		} else {
			// '@' <name>
			f.exprs = append(f.exprs, &filterAttrib2{sp, key})
		}

	case tokIdentifier:
		var sp, tag string
		toks, sp, tag, err = c.parseName(toks)
		if err != nil {
			return nil, err
		}

		switch toks.peekID() {
		case tokEqual:
			// ident '=' string
			var tok token
			tok, toks = toks.consume(1).next()
			if tok.id != tokString {
				return nil, ErrPathSyntax
			}
			f.exprs = append(f.exprs, &filterChildText2{sp, tag, tok.value.toString()})

		case tokLParen:
			var tok token
			tok, toks = toks.consume(1).next()
			if tok.id != tokRParen || tag != "text" {
				return nil, ErrPathSyntax
			}
			if toks.peekID() == tokEqual {
				// ident '(' ')' '=' string
				tok, toks = toks.consume(1).next()
				if tok.id != tokString {
					return nil, ErrPathSyntax
				}
				f.exprs = append(f.exprs, &filterTextByValue2{tok.value.toString()})
			} else {
				// ident '(' ')'
				f.exprs = append(f.exprs, &filterText2{})
			}

		default:
			// ident
			f.exprs = append(f.exprs, &filterChild2{sp, tag})
		}

	default:
		return nil, ErrPathSyntax
	}

	return toks, nil
}

//
// pather
//

// A pather is helper object that traverses an element tree using
// a Path object.  It collects and deduplicates all elements matching
// the path query.
type pather2 struct {
}

// A node represents an element and the remaining path segments that
// should be applied against it by the pather.
type node2 struct {
	e        *Element
	segments []segment2
}

type candidates struct {
	list  []*Element
	table map[*Element]bool
}

func newCandidates() candidates {
	return candidates{
		list:  make([]*Element, 0),
		table: make(map[*Element]bool),
	}
}

func (c *candidates) merge(other candidates) {
	for _, can := range other.list {
		c.add(can)
	}
}

func (c *candidates) add(e *Element) {
	if !c.table[e] {
		c.table[e] = true
		c.list = append(c.list, e)
	}
}

// traverse follows the path from the element e, collecting
// and then returning all elements that match the path's selectors
// and filters.
func (p *pather2) traverse(e *Element, path Path2) []*Element {
	out := newCandidates()

	var queue fifo
	for queue.add(node2{e, path.segments}); queue.len() > 0; {
		n := queue.remove().(node2)
		seg, remain := n.segments[0], n.segments[1:]

		candidates := p.evalSegment(n.e, seg)

		if len(remain) == 0 {
			out.merge(candidates)
		} else {
			for _, e := range candidates.list {
				queue.add(node2{e, remain})
			}
		}
	}

	return out.list
}

func (p *pather2) evalSegment(e *Element, s segment2) candidates {
	out := newCandidates()

	for _, ex := range s.exprs {
		out.merge(p.evalSegmentExpr(e, ex))
	}

	return out
}

func (p *pather2) evalSegmentExpr(e *Element, expr segmentExpr2) candidates {
	out := expr.sel.eval(e)

	if len(out.list) > 0 {
		for _, f := range expr.filters {
			out = p.evalFilter(e, f, out)
			if len(out.list) == 0 {
				break
			}
		}
	}

	return out
}

func (p *pather2) evalFilter(e *Element, f filter2, in candidates) candidates {
	out := newCandidates()

	for _, expr := range f.exprs {
		out.merge(expr.eval(e, in))
	}

	return out
}

// selectRoot selects the element's root node.
type selectRoot2 struct {
}

func (s *selectRoot2) eval(e *Element) candidates {
	root := e
	for root.parent != nil {
		root = root.parent
	}
	out := newCandidates()
	out.add(root)
	return out
}

// selectSelf selects the current element into the candidate list.
type selectSelf2 struct {
}

func (s *selectSelf2) eval(e *Element) candidates {
	out := newCandidates()
	out.add(e)
	return out
}

// selectParent selects the element's parent into the candidate list.
type selectParent2 struct {
}

func (s *selectParent2) eval(e *Element) candidates {
	out := newCandidates()

	if e.parent != nil {
		out.add(e.parent)
	}

	return out
}

// selectChildren selects the element's child elements into the candidate
// list.
type selectChildren2 struct {
}

func (s *selectChildren2) eval(e *Element) candidates {
	out := newCandidates()

	for _, child := range e.Child {
		if child, ok := child.(*Element); ok {
			out.add(child)
		}
	}

	return out
}

// selectChildrenByTag selects into the candidate list all child elements of
// the element having the specified tag.
type selectChildrenByTag2 struct {
	space string
	tag   string
}

func (s *selectChildrenByTag2) eval(e *Element) candidates {
	out := newCandidates()

	for _, ch := range e.Child {
		if ch, ok := ch.(*Element); ok && spaceMatch(s.space, ch.Space) && s.tag == ch.Tag {
			out.add(ch)
		}
	}

	return out
}

// selectDescendants selects all descendant child elements of the element into
// the candidate list.
type selectDescendants2 struct {
}

func (s *selectDescendants2) eval(e *Element) candidates {
	out := newCandidates()

	var queue fifo
	for queue.add(e); queue.len() > 0; {
		e := queue.remove().(*Element)
		out.add(e)
		for _, ch := range e.Child {
			if ch, ok := ch.(*Element); ok {
				queue.add(ch)
			}
		}
	}

	return out
}

// filterIndex filters the candidate list, keeping only the candidate at the
// specified index.
type filterIndex2 struct {
	index int
}

func (f *filterIndex2) eval(e *Element, in candidates) candidates {
	out := newCandidates()

	if f.index >= 0 {
		if f.index < len(in.list) {
			out.add(in.list[f.index])
		}
	} else {
		if -f.index <= len(in.list) {
			out.add(in.list[len(in.list)+f.index])
		}
	}

	return out
}

// filterAttrib filters the candidate list for elements having the specified
// attribute.
type filterAttrib2 struct {
	space string
	key   string
}

func (f *filterAttrib2) eval(e *Element, in candidates) candidates {
	out := newCandidates()

	for _, ch := range in.list {
		for _, a := range ch.Attr {
			if spaceMatch(f.space, a.Space) && f.key == a.Key {
				out.add(ch)
				break
			}
		}
	}

	return out
}

// filterAttribValue filters the candidate list for elements having the
// specified attribute with the specified value.
type filterAttribValue2 struct {
	space string
	key   string
	value string
}

func (f *filterAttribValue2) eval(e *Element, in candidates) candidates {
	out := newCandidates()

	for _, ch := range in.list {
		for _, a := range ch.Attr {
			if spaceMatch(f.space, a.Space) && f.key == a.Key && f.value == a.Value {
				out.add(ch)
				break
			}
		}
	}

	return out
}

// filterChild filters the candidate list for elements having a child element
// with the specified tag.
type filterChild2 struct {
	space string
	tag   string
}

func (f *filterChild2) eval(e *Element, in candidates) candidates {
	out := newCandidates()

	for _, ch := range in.list {
		for _, cc := range ch.Child {
			if cc, ok := cc.(*Element); ok && spaceMatch(f.space, cc.Space) && f.tag == cc.Tag {
				out.add(ch)
			}
		}
	}

	return out
}

// filterChildText filters the candidate list for elements having a child
// element with the specified tag and text.
type filterChildText2 struct {
	space string
	tag   string
	value string
}

func (f *filterChildText2) eval(e *Element, in candidates) candidates {
	out := newCandidates()

	for _, ch := range in.list {
		for _, cc := range ch.Child {
			if cc, ok := cc.(*Element); ok && spaceMatch(f.space, cc.Space) && f.tag == cc.Tag && f.value == cc.Text() {
				out.add(ch)
			}
		}
	}

	return out
}

// filterText filters the candidate list for elements having text.
type filterText2 struct {
}

func (s *filterText2) eval(e *Element, in candidates) candidates {
	out := newCandidates()

	for _, ch := range in.list {
		if ch.Text() != "" {
			out.add(ch)
		}
	}

	return out
}

// filterTextByValue filters the candidate list for elements having
// text equal to the specified value.
type filterTextByValue2 struct {
	value string
}

func (f *filterTextByValue2) eval(e *Element, in candidates) candidates {
	out := newCandidates()

	for _, ch := range in.list {
		if ch.Text() == f.value {
			out.add(ch)
		}
	}

	return out
}

//
// tokenizer
//

type tokenID uint8

const (
	tokNil tokenID = iota
	tokSep
	tokSepRecurse
	tokLBracket
	tokRBracket
	tokLParen
	tokRParen
	tokUnion
	tokEqual
	tokColon
	tokAt
	tokSelf
	tokParent
	tokChildren
	tokString
	tokIdentifier
	tokNumber
	tokEOL
)

const (
	lNil uint8 = iota
	lIde       // identifer
	lLbr       // lbracket
	lRbr       // rbracket
	lLpa       // lparen
	lRpa       // rparen
	lWld       // wildcard
	lSep       // separator
	lNum       // numeric
	lUni       // union
	lSub       // minus
	lDot       // dot
	lQuo       // quote
	lAtt       // attrib (@)
	lEqu       // equal
	lCol       // colon
)

const (
	xIdentStart = 1 << 6
	xIdentChar  = 1 << 7
	x0          = 0
	x1          = xIdentChar
	x2          = xIdentChar | xIdentStart
)

type token struct {
	id    tokenID
	value tstring
}

// A table mapping the first character of a lexeme to token lookup data.
var lexHint0 = [128]uint8{
	x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, // 0..7
	x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, // 8..15
	x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, // 16..23
	x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, // 24..31
	x0 | lNil, x0 | lNil, x0 | lQuo, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lQuo, // 32..39
	x0 | lLpa, x0 | lRpa, x0 | lWld, x0 | lNil, x0 | lNil, x1 | lSub, x1 | lDot, x0 | lSep, // 40..47
	x1 | lNum, x1 | lNum, x1 | lNum, x1 | lNum, x1 | lNum, x1 | lNum, x1 | lNum, x1 | lNum, // 48..55
	x1 | lNum, x1 | lNum, x0 | lCol, x0 | lNil, x0 | lNil, x0 | lEqu, x0 | lNil, x0 | lNil, // 56..63
	x0 | lAtt, x0 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, // 64..71
	x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, // 72..79
	x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, // 80..87
	x2 | lIde, x2 | lIde, x2 | lIde, x0 | lLbr, x0 | lNil, x0 | lRbr, x0 | lNil, x2 | lIde, // 88..95
	x0 | lNil, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, // 96..103
	x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, // 104..111
	x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, x2 | lIde, // 112..119
	x2 | lIde, x2 | lIde, x2 | lIde, x0 | lNil, x0 | lUni, x0 | lNil, x0 | lNil, x0 | lNil, // 120..127
}

type lexemeData struct {
	tokID    tokenID
	tokenize func(c *compiler2, s tstring) (t token, remain tstring, err error)
}

var lexToToken = []lexemeData{
	/*lNil*/ {tokID: tokNil},
	/*lIde*/ {tokenize: (*compiler2).tokenizeIdentifier},
	/*lLBr*/ {tokID: tokLBracket},
	/*lRBr*/ {tokID: tokRBracket},
	/*lLpa*/ {tokID: tokLParen},
	/*lRpa*/ {tokID: tokRParen},
	/*lWld*/ {tokID: tokChildren},
	/*lSep*/ {tokenize: (*compiler2).tokenizeSlash},
	/*lNum*/ {tokenize: (*compiler2).tokenizeNumber},
	/*lOra*/ {tokID: tokUnion},
	/*lSub*/ {tokenize: (*compiler2).tokenizeMinus},
	/*lDot*/ {tokenize: (*compiler2).tokenizeDot},
	/*lQuo*/ {tokenize: (*compiler2).tokenizeQuote},
	/*lAtt*/ {tokID: tokAt},
	/*lEqu*/ {tokID: tokEqual},
	/*lCol*/ {tokID: tokColon},
}

func (c *compiler2) tokenizePath(path string) (toks tokens, err error) {
	s := tstring(path).consumeWhitespace()
	toks = make(tokens, 0)

	for len(s) > 0 {
		tok, remain, err := c.tokenizeLexeme(s)
		if err != nil {
			return nil, err
		}
		if tok.id == tokNil {
			return nil, ErrPathSyntax
		}

		toks = append(toks, tok)

		s = remain.consumeWhitespace()
	}

	return toks, nil
}

func (c *compiler2) tokenizeLexeme(s tstring) (t token, remain tstring, err error) {
	if len(s) == 0 {
		return token{}, s, nil
	}

	r, sz := s.nextRune()

	// Use the first character of the string to look up lexeme data.
	var ldata lexemeData
	switch {
	case r < 128:
		ldata = lexToToken[lexHint0[r]&0x3f]
	case identifierStart(r):
		ldata = lexToToken[lIde]
	default:
		return token{}, s, ErrPathSyntax
	}

	// If the lexeme consists of only one character, we're done.
	if ldata.tokenize == nil {
		return token{ldata.tokID, ""}, s.consume(sz), nil
	}

	// Parse the rest of the lexeme.
	return ldata.tokenize(c, s)
}

func (c *compiler2) tokenizeIdentifier(s tstring) (t token, remain tstring, err error) {
	var ident tstring
	ident, remain = s.consumeWhile(identifier)
	return token{tokIdentifier, ident}, remain, nil
}

func (c *compiler2) tokenizeSlash(s tstring) (t token, remain tstring, err error) {
	if len(s) > 1 && s[1] == '/' {
		return token{tokSepRecurse, ""}, s.consume(2), nil
	}
	return token{tokSep, ""}, s.consume(1), nil
}

func (c *compiler2) tokenizeNumber(s tstring) (t token, remain tstring, err error) {
	var num tstring
	num, remain = s.consumeWhile(decimal)
	return token{tokNumber, num}, remain, nil
}

func (c *compiler2) tokenizeMinus(s tstring) (t token, remain tstring, err error) {
	var num tstring
	num, remain = s.consume(1).consumeWhile(decimal)
	if len(num) == 0 {
		return token{}, s, ErrPathSyntax
	}
	num = s[:len(num)+1]
	return token{tokNumber, num}, remain, nil
}

func (c *compiler2) tokenizeDot(s tstring) (t token, remain tstring, err error) {
	if len(s) > 1 && s[1] == '.' {
		return token{tokParent, ""}, s.consume(2), nil
	}
	return token{tokSelf, ""}, s.consume(1), nil
}

func (c *compiler2) tokenizeQuote(s tstring) (t token, remain tstring, err error) {
	quot := rune(s[0])
	s = s.consume(1)

	var scopy []rune
	var escNext bool
loop:
	for i, r := range s {
		switch {
		case escNext:
			if r >= 'a' && r <= 'z' {
				scopy = append(scopy, r) // TODO: parse escape code
			} else {
				scopy = append(scopy, r)
			}
			escNext = false

		case r == quot:
			s, remain = s[:i], s[i+1:]
			break loop

		case r == '\\':
			escNext = true
			if scopy == nil {
				scopy = make([]rune, 0)
				for _, rr := range s[:i] {
					scopy = append(scopy, rr)
				}
			}

		case scopy != nil:
			scopy = append(scopy, r)
		}
	}

	if scopy == nil {
		return token{tokString, s}, remain, nil
	}

	return token{tokString, tstring(scopy)}, remain, nil
}

//
// tokens
//

type tokens []token

func (t tokens) consume(n int) tokens {
	return t[n:]
}

func (t tokens) peekID() tokenID {
	if len(t) == 0 {
		return tokEOL
	}
	return t[0].id
}

func (t tokens) next() (tok token, remain tokens) {
	if len(t) == 0 {
		return token{id: tokEOL}, t
	}
	return t[0], t[1:]
}

//
// tstring
//

type tstring string

func (s tstring) consume(n int) tstring {
	return s[n:]
}

func (s tstring) consumeWhitespace() tstring {
	return s.consume(s.scanWhile(whitespace))
}

func (s tstring) scanWhile(fn func(r rune) bool) int {
	i := 0
	var r rune
	for _, r = range s {
		if !fn(r) {
			break
		}
		i++
	}
	return i
}

func (s tstring) consumeWhile(fn func(r rune) bool) (consumed, remain tstring) {
	i := s.scanWhile(fn)
	return s[:i], s[i:]
}

func (s tstring) nextRune() (r rune, sz int) {
	return utf8.DecodeRuneInString(s.toString())
}

func (s tstring) toString() string {
	// Convert the tstring to a string without making a copy.
	var out string
	src := (*reflect.StringHeader)(unsafe.Pointer(&s))
	dst := (*reflect.StringHeader)(unsafe.Pointer(&out))
	dst.Len = src.Len
	dst.Data = src.Data
	return out
}

func whitespace(r rune) bool {
	return r == ' ' || r == '\t'
}

func decimal(r rune) bool {
	return (r >= '0' && r <= '9')
}

func identifierStart(r rune) bool {
	if r < 128 {
		return (lexHint0[r] & xIdentStart) != 0
	}

	switch {
	case r >= 0xc0 && r <= 0xd6:
		return true
	case r >= 0xd8 && r <= 0xf6:
		return true
	case r >= 0xf8 && r <= 0x2ff:
		return true
	case r >= 0x370 && r <= 0x37d:
		return true
	case r >= 0x37f && r <= 0x1fff:
		return true
	case r >= 0x200c && r <= 0x200d:
		return true
	case r >= 0x2070 && r <= 0x218f:
		return true
	case r >= 0x2c00 && r <= 0x2fef:
		return true
	case r >= 0x3001 && r <= 0xd7ff:
		return true
	case r >= 0xf900 && r <= 0xfdcf:
		return true
	case r >= 0xfdf0 && r <= 0xfffd:
		return true
	default:
		return false
	}
}

func identifier(r rune) bool {
	// "-" | "." | [0-9] | #xB7 | [#x0300-#x036F] | [#x203F-#x2040]
	switch {
	case r < 128:
		return (lexHint0[r] & xIdentChar) != 0
	case identifierStart(r):
		return true
	case r == 0xb7:
		return true
	case r >= 0x300 && r <= 0x36f:
		return true
	case r >= 0x300 && r <= 0x36f:
		return true
	case r >= 0x203f && r <= 0x2040:
		return true
	default:
		return false
	}
}
