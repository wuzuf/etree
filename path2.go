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
	segments []segment
}

// CompilePath2 creates an optimized version of an XPath-like string that
// can be used to query elements in an element tree.
func CompilePath2(path string) (Path2, error) {
	var comp compiler
	segments := comp.parsePath(path)
	if comp.err != ErrPath("") {
		return Path2{nil}, comp.err
	}
	return Path2{segments}, nil
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
  <segmentUnion>  ::= <segmentExpr> ('|' <segmentExpr>)
  <segmentExpr>   ::= <selector> <filterWrapper>* | '(' <segmentExpr> ')'
  <selector>      ::= '.' | '..' | '*' | identifier
  <filterWrapper> ::= '[' <filterUnion> ']'
  <filterUnion>   ::= <filterExpr> ('|' <filterExpr>)*
  <filterExpr>    ::= <filterIndex> | <filterCompare> | <filterExist> | '(' <filterExpr> ')'
  <filterIndex>   ::= number
  <filterCompare> ::= <filterKey> '=' <filterValue>
  <filterExist>   ::= <filterKey>
  <filterKey>     ::= <keyIdent> | <keyFunc> | <keyAttrib>
  <filterValue>   ::= string
  <keyFunc>       ::= identifier '(' ')'
  <keyIdent>      ::= identifier
  <keyAttrib>     ::= '@' identifier

tokenizer
  consume
  peek
  consumeAndRemember
  flush
  restore

path
  []segmentUnion
segmentUnion
  []segmentExpr
segmentExpr
  selector
  []filterUnion
selector
  curr | parent | wildcard | tag
filterUnion
  []filterExpr
filterExpr
  filterIndex | filterAttribExist | filterAttribValue | filterTagExit | filterTagValue
*/

// A compiler generates a compiled path from a path string.
type compiler2 struct {
	err    error
	tokens []token
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
	tokAttrib
	tokCurr
	tokParent
	tokChildren
	tokText
	tokString
	tokIdent
	tokNum
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
	/*lAtt*/ {tok: tokAttrib},
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
	return token{tokIdent, ident}, remain, nil
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
	return token{tokNum, num}, remain, nil
}

func (c *compiler2) parseMinus(s tstring) (t token, remain tstring, err error) {
	var num tstring
	num, remain = s.consume(1).consumeWhile(decimal)
	if len(num) == 0 {
		return token{}, s, errPath
	}
	num = s[:len(num)+1]
	return token{tokNum, num}, remain, nil
}

func (c *compiler2) parseDot(s tstring) (t token, remain tstring, err error) {
	if len(s) > 1 && s[1] == '.' {
		return token{tokChildren, ""}, s.consume(2), nil
	}
	return token{tokCurr, ""}, s.consume(1), nil
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
	c.tokens = make([]token, 0)

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

type tstring string

func (s tstring) consume(n int) tstring {
	return s[n:]
}

func (s tstring) consumeWhitespace() tstring {
	return s.consume(s.scanWhile(whitespace))
}

func (s tstring) scanWhile(fn func(r rune) bool) int {
	var i int
	var r rune
	for i, r = range s {
		if !fn(r) {
			break
		}
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
