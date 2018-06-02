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

var errPathSyntax = errors.New("etree: path syntax error")

// TODO:
//  Parse escape codes in strings
//  Write selector and filter apply functions

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

var errPath = errors.New("invalid path")

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
  <selector>      ::= '.' | '..' | '*' | identifier
  <filterWrapper> ::= '[' <filter> ']'
  <filter>        ::= <filterExpr> ('|' <filterExpr>)*
  <filterExpr>    ::= <filterIndex> | <filterAttrib> | <filterChild> | <filterFunc> | '(' <filter> ')'
  <filterIndex>   ::= number
  <filterAttrib>  ::= '@' ident | '@' ident '=' string
  <filterChild>   ::= ident | ident '=' string
  <filterFunc>    ::= ident '(' ')' | ident '(' ')' '=' string
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
	//	apply(e *Element, p *pather)
}

type filterExpr2 interface {
	//	apply(p *pather)
}

var rootSegment = segment2{
	exprs: []segmentExpr2{
		segmentExpr2{
			sel: selectRoot2{},
		},
	},
}

var descendantsSegment = segment2{
	exprs: []segmentExpr2{
		segmentExpr2{
			sel: selectDescendants2{},
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
		return errPathSyntax
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
			return errPathSyntax
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
			return nil, errPathSyntax
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
			return nil, errPathSyntax
		}

		var tok token
		tok, toks = toks.next()
		if tok.id != tokRBracket {
			return nil, errPathSyntax
		}

		e.filters = append(e.filters, f)
	}

	s.exprs = append(s.exprs, e)
	return toks, nil
}

func (c *compiler2) parseSelector2(s *selector2, toks tokens) (remain tokens, err error) {
	// <selector> ::= '.' | '..' | '*' | identifier

	var tok token
	tok, toks = toks.next()
	switch tok.id {
	case tokSelf:
		*s = selectSelf2{}
	case tokParent:
		*s = selectParent2{}
	case tokChildren:
		*s = selectChildren2{}
	case tokIdentifier:
		*s = selectChildrenByTag2{tok.value}
	default:
		return nil, errPathSyntax
	}

	return toks, nil
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

	var tok token
	tok, toks = toks.next()

	switch tok.id {
	case tokLParen:
		// '(' <filter> ')'
		var ff filter2
		toks, err = c.parseFilter2(&ff, toks)
		if err != nil {
			return nil, err
		}
		tok, toks = toks.next()
		if tok.id != tokRParen {
			return nil, errPathSyntax
		}
		f.exprs = append(f.exprs, ff.exprs...)

	case tokNumber:
		// number
		index, _ := strconv.Atoi(string(tok.value))
		if index > 0 {
			index--
		}
		f.exprs = append(f.exprs, filterIndex2{index})

	case tokAt:
		tok, toks = toks.next()
		if tok.id != tokIdentifier {
			return nil, errPathSyntax
		}
		name := tok.value

		if toks.peekID() == tokEqual {
			// '@' ident '=' string
			tok, toks = toks.consume(1).next()
			if tok.id != tokString {
				return nil, errPathSyntax
			}
			f.exprs = append(f.exprs, filterAttribByValue2{name, tok.value})
		} else {
			// '@' ident
			f.exprs = append(f.exprs, filterAttrib2{name})
		}

	case tokIdentifier:
		name := tok.value

		switch toks.peekID() {
		case tokEqual:
			// ident '=' string
			tok, toks = toks.consume(1).next()
			if tok.id != tokString {
				return nil, errPathSyntax
			}
			f.exprs = append(f.exprs, filterTagByValue2{name, tok.value})

		case tokLParen:
			tok, toks = toks.consume(1).next()
			if tok.id != tokRParen || name != "text" {
				return nil, errPathSyntax
			}
			tok, toks = toks.next()
			if tok.id == tokEqual {
				// ident '(' ')' '=' string
				tok, toks = toks.next()
				if tok.id != tokString {
					return nil, errPathSyntax
				}
				f.exprs = append(f.exprs, filterTextByValue2{tok.value})
			} else {
				// ident '(' ')'
				f.exprs = append(f.exprs, filterText2{})
			}

		default:
			// ident
			f.exprs = append(f.exprs, filterTag2{name})
		}

	default:
		return nil, errPathSyntax
	}

	return toks, nil
}

// selectRoot selects the element's root node.
type selectRoot2 struct {
}

// selectSelf selects the current element into the candidate list.
type selectSelf2 struct {
}

// selectParent selects the element's parent into the candidate list.
type selectParent2 struct {
}

// selectChildren selects the element's child elements into the candidate
// list.
type selectChildren2 struct {
}

// selectChildrenByTag selects into the candidate list all child elements of
// the element having the specified tag.
type selectChildrenByTag2 struct {
	tag tstring
}

// selectDescendants selects all descendant child elements of the element into
// the candidate list.
type selectDescendants2 struct {
}

// filterIndex filters the candidate list, keeping only the candidate at the
// specified index.
type filterIndex2 struct {
	index int
}

// filterAttrib filters the candidate list for elements having the specified
// attribute.
type filterAttrib2 struct {
	attr tstring
}

// filterAttribByValue filters the candidate list for elements having the
// specified attribute with the specified value.
type filterAttribByValue2 struct {
	attr  tstring
	value tstring
}

// filterTag filters the candidate list for elements having a child element
// with the specified tag.
type filterTag2 struct {
	tag tstring
}

// filterTagByValue filters the candidate list for elements having a child
// element with the specified tag and text.
type filterTagByValue2 struct {
	tag   tstring
	value tstring
}

// filterText filters the candidate list for elements having text.
type filterText2 struct {
}

// filterTextByValue filters the candidate list for elements having
// text equal to the specified value.
type filterTextByValue2 struct {
	value tstring
}

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
	x1 | lNum, x1 | lNum, x0 | lNil, x0 | lNil, x0 | lNil, x0 | lEqu, x0 | lNil, x0 | lNil, // 56..63
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
			return nil, errPath
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
		return token{}, s, errPath
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
		return token{}, s, errPath
	}
	num = s[:len(num)+1]
	return token{tokNumber, num}, remain, nil
}

func (c *compiler2) tokenizeDot(s tstring) (t token, remain tstring, err error) {
	if len(s) > 1 && s[1] == '.' {
		return token{tokChildren, ""}, s.consume(2), nil
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
	// Convert the tstring to a string without making a copy.
	var dstString string
	src := (*reflect.StringHeader)(unsafe.Pointer(&s))
	dst := (*reflect.StringHeader)(unsafe.Pointer(&dstString))
	dst.Len = src.Len
	dst.Data = src.Data

	return utf8.DecodeRuneInString(dstString)
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
