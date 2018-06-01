// Copyright 2015 Brett Vickers.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package etree

import (
	"errors"
	"reflect"
	"unicode/utf8"
	"unsafe"
)

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
	segUnions []segmentUnion2 // take union of segment results
}

// CompilePath2 creates an optimized version of an XPath-like string that
// can be used to query elements in an element tree.
func CompilePath2(path string) (Path2, error) {
	return Path2{}, nil
	// var comp compiler2
	// segments := comp.parsePath(path)
	// if comp.err != ErrPath("") {
	// 	return Path2{nil}, comp.err
	// }
	// return Path2{segments}, nil
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
  /						sep
  //					sep_recurse
  [						lbracket
  ]						rbracket
  (						lparen
  )						rparen
  |						or
  =						equal
  @						attrib
  .						curr
  ..					parent
  *						wildcard
  '[^']*'				string
  "[^"]*'				string
  text()				function
  [a-zA-Z][a-z_A-Z0-9]*	identifier
  [-+]?[0-9][0-9]* 		number

Example:
  //(book|pamphlet[@size='small'])/*[(@author='a'|@author='b')]

Grammar:
  <path>          ::= <sep>? (<segmentUnion> <sep>)* <segmentUnion>?
  <sep>           ::= '/' | '//'
  <segmentUnion>  ::= <segment> ('|' <segment>)
  <segment>       ::= <selector> <filterWrapper>* | '(' <segment> ')'
  <selector>      ::= '.' | '..' | '*' | identifier
  <filterWrapper> ::= '[' <filterUnion> ']'
  <filterUnion>   ::= <filter> ('|' <filter>)* | '(' <filterUnion> ')'
  <filter>        ::= <filterIndex> | <filterCompare> | <filterExist> | '(' <filter> ')'
  <filterIndex>   ::= number
  <filterCompare> ::= <filterKey> '=' <filterValue>
  <filterExist>   ::= <filterKey>
  <filterKey>     ::= <keyIdent> | <keyFunc> | <keyAttrib>
  <filterValue>   ::= string
  <keyFunc>       ::= identifier '(' ')'
  <keyIdent>      ::= identifier
  <keyAttrib>     ::= '@' identifier
*/

type segmentUnion2 struct {
	segments []segment2
}

type segment2 struct {
	sel          selector2
	filterUnions []filterUnion2 // apply filters in sequence
}

type selector2 interface {
	//	apply(e *Element, p *pather)
}

type filterUnion2 struct {
	filters []filter2 // take union of all filter results
}

type filter2 interface {
	//	apply(p *pather)
}

// A compiler generates a compiled path from a path string.
type compiler2 struct {
	err    error
	tokens tokenList
}

func (c *compiler2) parsePath(p *Path2, tokens tokenList) (err error) {
	// Check for an absolute path (leading with '/' or '//').
	tok := tokens.peek()
	switch tok.id {
	case tokSep:
		// insert root selector
		tokens = tokens.consume(1)
	case tokSepRecurse:
		// insert root selector
		// insert descendants selector
		tokens = tokens.consume(1)
	case tokEOL:
		return errors.New("syntax error")
	}

loop:
	for len(tokens) > 0 {
		var u segmentUnion2
		tokens, err = c.parseSegmentUnion2(&u, tokens)
		if err != nil {
			return err
		}

		p.segUnions = append(p.segUnions, u)

		tok, tokens = tokens.next()
		switch tok.id {
		case tokSep:
			// do nothing
		case tokSepRecurse:
			// insert descendants selector
		case tokEOL:
			break loop
		default:
			return errors.New("syntax error")
		}
	}

	return nil
}

func (c *compiler2) parseSegmentUnion2(u *segmentUnion2, tokens tokenList) (remain tokenList, err error) {
	// <segmentUnion> ::= <segment> ('|' <segment>)

	// Parse one or more segments.
	for {
		var s segment2
		tokens, err = c.parseSegment2(&s, tokens)
		if err != nil {
			return nil, err
		}

		u.segments = append(u.segments, s)

		if tokens.peek().id != tokOr {
			break
		}
		tokens = tokens.consume(1)
	}

	return tokens, nil
}

func (c *compiler2) parseSegment2(s *segment2, tokens tokenList) (remain tokenList, err error) {
	// <segment> ::= <selector> <filterWrapper>* | '(' <segment> ')'

	// Check for parentheses.
	tok := tokens.peek()
	if tok.id == tokLParen {
		tokens, err = c.parseSegment2(s, tokens.consume(1))
		if err != nil {
			return nil, err
		}
		tok, tokens = tokens.next()
		if tok.id != tokRParen {
			return nil, errors.New("syntax error")
		}
		return tokens, nil
	}

	// Parse the selector.
	tokens, err = c.parseSelector2(&s.sel, tokens)
	if err != nil {
		return nil, err
	}

	// Parse zero or more wrapped filter expressions.
	for {
		tok = tokens.peek()
		if tok.id != tokLBracket {
			break
		}

		var f filterUnion2
		tokens, err = c.parseFilterUnion2(&f, tokens.consume(1))
		if err != nil {
			return nil, errors.New("syntax error")
		}

		tok, tokens = tokens.next()
		if tok.id != tokRBracket {
			return nil, errors.New("syntax error")
		}

		s.filterUnions = append(s.filterUnions, f)
	}

	return tokens, nil
}

func (c *compiler2) parseSelector2(s *selector2, tokens tokenList) (remain tokenList, err error) {
	// selector> ::= '.' | '..' | '*' | identifier

	var tok token
	tok, tokens = tokens.next()
	switch tok.id {
	case tokCurrent:
		// insert a current selector
	case tokParent:
		// insert a parent selector
	case tokChildren:
		// insert a children selector
	case tokIdentifier:
		// insert a tag selector
	default:
		return nil, errors.New("syntax error")
	}

	return tokens, nil
}

func (c *compiler2) parseFilterUnion2(fu *filterUnion2, tokens tokenList) (remain tokenList, err error) {
	// <filterUnion> ::= <filter> ('|' <filter>)* | '(' <filterUnion> ')'

	tok := tokens.peek()
	if tok.id == tokLParen {
		tokens, err = c.parseFilterUnion2(fu, tokens.consume(1))
		if err != nil {
			return nil, err
		}
		tok, tokens = tokens.next()
		if tok.id != tokRParen {
			return nil, errors.New("syntax error")
		}
		return tokens, nil
	}

	// Parse one or more filter expressions.
	for {
		var f filter2
		tokens, err = c.parseFilter2(&f, tokens)
		if err != nil {
			return nil, err
		}

		fu.filters = append(fu.filters, f)

		tok := tokens.peek()
		if tok.id != tokOr {
			break
		}
		tokens = tokens.consume(1)
	}

	return tokens, nil
}

func (c *compiler2) parseFilter2(f *filter2, tokens tokenList) (remain tokenList, err error) {
	// <filter> ::= <filterIndex> | <filterCompare> | <filterExist> | '(' <filter> ')'

	var tok token
	tok, tokens = tokens.next()

	// Check for parentheses.
	switch tok.id {
	case tokLParen:
		tokens, err = c.parseFilter2(f, tokens)
		if err != nil {
			return nil, err
		}
		tok, tokens = tokens.next()
		if tok.id != tokRParen {
			return nil, errors.New("syntax error")
		}

	case tokNumber:
		// insert an index filter
		_ = tok.value

	case tokAt:
		tok, tokens = tokens.next()
		if tok.id != tokIdentifier {
			return nil, errors.New("syntax error")
		}
		name := tok.value

		if tokens.peek().id == tokEqual {
			tok, tokens = tokens.consume(1).next()
			if tok.id != tokString {
				return nil, errors.New("syntax error")
			}
			value := tok.value
			// insert an attribute-value filter
			_, _ = name, value
		} else {
			// insert an attribute-exist filter
			_ = name
		}

	case tokIdentifier:
		name := tok.value

		tok = tokens.peek()
		switch tok.id {
		case tokEqual:
			tok, tokens = tokens.consume(1).next()
			if tok.id != tokString {
				return nil, errors.New("syntax error")
			}
			value := tok.value
			// insert a tag-value filter
			_, _ = name, value

		case tokLParen:
			tok, tokens = tokens.consume(1).next()
			if tok.id != tokRParen {
				return nil, errors.New("syntax error")
			}
			tok, tokens = tokens.next()
			if tok.id != tokEqual {
				return nil, errors.New("syntax error")
			}
			tok, tokens = tokens.next()
			if tok.id != tokString {
				return nil, errors.New("syntax error")
			}
			if name != "text" {
				return nil, errors.New("syntax error")
			}
			value := tok.value
			// insert a text filter
			_ = value

		default:
			// insert a tag-exist filter
			_ = name
		}

	default:
		return nil, errors.New("syntax error")
	}

	return tokens, nil
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
	tokOr
	tokEqual
	tokAt
	tokCurrent
	tokParent
	tokChildren
	tokText
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
	lOra       // or
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

// A table mapping the first character of a lexeme to a token or parser.
var tbl0 = [128]uint8{
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
	x2 | lIde, x2 | lIde, x2 | lIde, x0 | lNil, x0 | lOra, x0 | lNil, x0 | lNil, x0 | lNil, // 120..127
}

type lexeme struct {
	tok   tokenID
	parse func(c *compiler2, s tstring) (t token, remain tstring, err error)
}

var ll = []lexeme{
	/*lNil*/ {tok: tokNil},
	/*lIde*/ {parse: (*compiler2).parseIdentifier},
	/*lLBr*/ {tok: tokLBracket},
	/*lRBr*/ {tok: tokRBracket},
	/*lLpa*/ {tok: tokLParen},
	/*lRpa*/ {tok: tokRParen},
	/*lWld*/ {tok: tokChildren},
	/*lSep*/ {parse: (*compiler2).parseSlash},
	/*lNum*/ {parse: (*compiler2).parseNumber},
	/*lOra*/ {tok: tokOr},
	/*lSub*/ {parse: (*compiler2).parseMinus},
	/*lDot*/ {parse: (*compiler2).parseDot},
	/*lQuo*/ {parse: (*compiler2).parseQuote},
	/*lAtt*/ {tok: tokAt},
	/*lEqu*/ {tok: tokEqual},
}

func (c *compiler2) parseToken(s tstring) (t token, remain tstring, err error) {
	if len(s) == 0 {
		return token{}, s, nil
	}

	r, sz := s.nextRune()

	// Use the first character of the string to look up lexeme data.
	var lex lexeme
	switch {
	case r < 128:
		lex = ll[tbl0[r]&0x1f]
	case identifierStart(r):
		lex = ll[lIde]
	default:
		return token{}, s, errPath
	}

	// If the lexeme consists of only one character, we're done.
	if lex.parse == nil {
		return token{lex.tok, ""}, s.consume(sz), nil
	}

	// Parse the rest of the lexeme.
	return lex.parse(c, s)
}

func (c *compiler2) parseIdentifier(s tstring) (t token, remain tstring, err error) {
	var ident tstring
	ident, remain = s.consumeWhile(identifier)
	return token{tokIdentifier, ident}, remain, nil
}

func (c *compiler2) parseSlash(s tstring) (t token, remain tstring, err error) {
	if len(s) > 1 && s[1] == '/' {
		return token{tokSepRecurse, ""}, s.consume(2), nil
	}
	return token{tokSep, ""}, s.consume(1), nil
}

func (c *compiler2) parseNumber(s tstring) (t token, remain tstring, err error) {
	var num tstring
	num, remain = s.consumeWhile(decimal)
	return token{tokNumber, num}, remain, nil
}

func (c *compiler2) parseMinus(s tstring) (t token, remain tstring, err error) {
	var num tstring
	num, remain = s.consume(1).consumeWhile(decimal)
	if len(num) == 0 {
		return token{}, s, errPath
	}
	num = s[:len(num)+1]
	return token{tokNumber, num}, remain, nil
}

func (c *compiler2) parseDot(s tstring) (t token, remain tstring, err error) {
	if len(s) > 1 && s[1] == '.' {
		return token{tokChildren, ""}, s.consume(2), nil
	}
	return token{tokCurrent, ""}, s.consume(1), nil
}

func (c *compiler2) parseQuote(s tstring) (t token, remain tstring, err error) {
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

func (c *compiler2) tokenizePath(path string) error {
	s := tstring(path).consumeWhitespace()
	c.tokens = make(tokenList, 0)

	for len(s) > 0 {
		tok, remain, err := c.parseToken(s)
		if err != nil {
			return err
		}
		if tok.id == tokNil {
			return errPath
		}

		c.tokens = append(c.tokens, tok)

		s = remain.consumeWhitespace()
	}

	return nil
}

//
// tokenList
//

type tokenList []token

func (t tokenList) consume(n int) tokenList {
	return t[n:]
}

func (t tokenList) peek() token {
	if len(t) == 0 {
		return token{id: tokEOL}
	}
	return t[0]
}

func (t tokenList) next() (tok token, remain tokenList) {
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
		return (tbl0[r] & xIdentStart) != 0
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
		return (tbl0[r] & xIdentChar) != 0
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
