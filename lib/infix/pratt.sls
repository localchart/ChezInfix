;;;
;;;Part of: ChezInfix
;;;Contents: infix to prefix syntax using Pratt parsing
;;;Date: Mon May  5, 2014
;;;
;;;Abstract
;;;
;;;	This file  implements the INFIX  syntax.  It is  an infix to  prefix notation
;;;	transformer supporting  the tradition mathematical expressions  infix syntax.
;;;	The transformer is based on a Pratt parser as exposed in:
;;;
;;;        Pratt, Vaughan.  "Top Down  Operator Precedence".  Massachussets Institute
;;;        of Technology.  Proceedings of the 1st Annual ACM SIGACT-SIGPLAN Symposium
;;;        on Principles of Programming Languages (1973).
;;;
;;;Copyright (c) 2014, 2017 Marco Maggi <marco.maggi-ipsu@poste.it>
;;;
;;;This program is free software: you can  redistribute it and/or modify it under the
;;;terms  of  the GNU  General  Public  License as  published  by  the Free  Software
;;;Foundation,  either version  3  of the  License,  or (at  your  option) any  later
;;;version.
;;;
;;;This program is  distributed in the hope  that it will be useful,  but WITHOUT ANY
;;;WARRANTY; without  even the implied warranty  of MERCHANTABILITY or FITNESS  FOR A
;;;PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;;;
;;;You should have received a copy of  the GNU General Public License along with this
;;;program.  If not, see <http://www.gnu.org/licenses/>.
;;;


;;;; copyright notice for the XOR macro
;;;
;;;Copyright (c) 2008 Derick Eddington
;;;
;;;Permission is hereby  granted, free of charge,  to any person obtaining  a copy of
;;;this software and associated documentation files  (the "Software"), to deal in the
;;;Software  without restriction,  including without  limitation the  rights to  use,
;;;copy, modify,  merge, publish, distribute,  sublicense, and/or sell copies  of the
;;;Software,  and to  permit persons  to whom  the Software  is furnished  to do  so,
;;;subject to the following conditions:
;;;
;;;The above  copyright notice and  this permission notice  shall be included  in all
;;;copies or substantial portions of the Software.
;;;
;;;Except as  contained in this  notice, the name(s)  of the above  copyright holders
;;;shall not be  used in advertising or  otherwise to promote the sale,  use or other
;;;dealings in this Software without prior written authorization.
;;;
;;;THE  SOFTWARE IS  PROVIDED  "AS IS",  WITHOUT  WARRANTY OF  ANY  KIND, EXPRESS  OR
;;;IMPLIED, INCLUDING BUT  NOT LIMITED TO THE WARRANTIES  OF MERCHANTABILITY, FITNESS
;;;FOR A  PARTICULAR PURPOSE AND NONINFRINGEMENT.   IN NO EVENT SHALL  THE AUTHORS OR
;;;COPYRIGHT HOLDERS BE LIABLE FOR ANY  CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
;;;AN ACTION OF  CONTRACT, TORT OR OTHERWISE,  ARISING FROM, OUT OF  OR IN CONNECTION
;;;WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.


#!r6rs
(library (infix pratt)
  (export infix incr! decr! != xor factorial)
  (import (for (rnrs (6))
	    run expand (meta 2)))


;;;; helpers

(define-syntax define-auxiliary-syntaxes
  (syntax-rules ()
    ((_ ?key)
     (define-syntax ?key (syntax-rules ())))
    ((_ ?key0 ?key1 . ?keys)
     (begin
       (define-auxiliary-syntaxes ?key0)
       (define-auxiliary-syntaxes ?key1 . ?keys)))
    ))


;;;; more operators

(define (factorial N)
  (assert (and (integer? N)
	       (not (negative? N))))
  (let recur ((N N)
	      (R 1))
    (if (zero? N)
	R
      (recur (- N 1) (* N R)))))

(define !=
  (case-lambda
   ((arg)
    #f)
   ((arg1 arg2)
    (not (= arg1 arg2)))
   ((arg1 arg2 . arg*)
    (not (apply = arg1 arg2 arg*)))))

;;; --------------------------------------------------------------------

;;The identifiers ++ and -- would be better  choices than INCR! and DECR!, but ++ and
;;-- are not valid identifiers according to R6RS.
(define-auxiliary-syntaxes incr! decr!)

(define-syntax pre-incr
  (lambda (stx)
    (syntax-case stx ()
      ((_ ?id)
       (identifier? #'?id)
       #'(begin
	   (set! ?id (+ ?id 1))
	   ?id))
      ((_ ?expr)
       #'(+ ?expr 1))
      (_
       (syntax-violation 'pre-incr "invalid pre-increment operation" (syntax->datum stx))))))

(define-syntax pre-decr
  (lambda (stx)
    (syntax-case stx ()
      ((_ ?id)
       (identifier? #'?id)
       #'(begin
	   (set! ?id (- ?id 1))
	   ?id))
      ((_ ?expr)
       #'(- ?expr 1))
      (_
       (syntax-violation 'pre-decr "invalid pre-decrement operation" (syntax->datum stx))))))

(define-syntax post-incr
  (lambda (stx)
    (syntax-case stx ()
      ((_ ?id)
       (identifier? #'?id)
       #'(let ((v ?id))
	   (set! ?id (+ ?id 1))
	   v))
      ((_ ?expr)
       #'(+ ?expr 1))
      (_
       (syntax-violation 'post-incr "invalid post-increment operation" (syntax->datum stx))))))

(define-syntax post-decr
  (lambda (stx)
    (syntax-case stx ()
      ((_ ?id)
       (identifier? #'?id)
       #'(let ((v ?id))
	   (set! ?id (- ?id 1))
	   v))
      ((_ ?expr)
       #'(- ?expr 1))
      (_
       (syntax-violation 'post-decr "invalid post-decrement operation" (syntax->datum stx))))))

;;; --------------------------------------------------------------------

(define-syntax xor
  (syntax-rules ()
    ((_ expr ...)
     (xor-aux #F expr ...))))

(define-syntax xor-aux
  (syntax-rules ()
    ((_ r)
     r)
    ((_ r expr)
     (let ((x expr))
       (if r
           (and (not x) r)
	 x)))
    ((_ r expr0 expr ...)
     (let ((x expr0))
       (and (or (not r) (not x))
	    (let ((n (or r x)))
	      (xor-aux n expr ...)))))))


(define-syntax infix
  (let ()

    (define-syntax receive-and-return
      (syntax-rules ()
	((_ (?var0 ?var ...) ?expr ?body0 ?body ...)
	 (call-with-values
	     (lambda () ?expr)
	   (lambda (?var0 ?var ...)
	     ?body0 ?body ...
	     (values ?var0 ?var ...))))
	))

    ;;NOTE This definition  of DEFINE-CONSTANT is the  one I prefer, but  it does not
    ;;work with Sagittarius (because its expander is not fully R6RS compliant).
    ;;
    ;; (define-syntax define-constant
    ;;   (syntax-rules ()
    ;;     ((_ ?id ?expr)
    ;;      (begin
    ;;        (define shadow ?expr)
    ;;        (define-syntax ?id
    ;; 	 (identifier-syntax shadow))))
    ;;     ))
    ;;
    ;;The version below works with Sagittarius, too.  (Marco Maggi; Thu Jun 5, 2014)
    (define-syntax define-constant
      (lambda (stx)
	(syntax-case stx ()
	  ((_ ?id ?expr)
	   (with-syntax (((SHADOW) (generate-temporaries '(#f))))
	     #'(begin
		 (define SHADOW ?expr)
		 (define-syntax ?id
		   (identifier-syntax SHADOW)))))
	  )))

    (define-syntax case-identifiers
      (syntax-rules (else)
	((_ ?expr ((?id0 ?id ...) ?body0 ?body ...) ... (else ?else-body0 ?else-body ...))
	 (let ((obj ?expr))
	   (define (else-branch)
	     ?else-body0 ?else-body ...)
	   (if (identifier? obj)
	       (cond ((or (free-identifier=? obj #'?id0)
			  (free-identifier=? obj #'?id)
			  ...)
		      ?body0 ?body ...)
		     ...
		     (else
		      (else-branch)))
	     (else-branch))))
	((_ ?expr ((?id0 ?id ...) ?body0 ?body ...) ...)
	 (let ((obj ?expr))
	   (if (identifier? obj)
	       (cond ((or (free-identifier=? obj #'?id0)
			  (free-identifier=? obj #'?id)
			  ...)
		      ?body0 ?body ...)
		     ...)
	     (values))))
	))

    (define-syntax define-syntax-rule
      (syntax-rules ()
	((_ (?name ?arg ... . ?rest) ?body0 ?body* ...)
	 (define-syntax ?name
	   (syntax-rules ()
	     ((?name ?arg ... . ?rest)
	      (begin ?body0 ?body* ...))
	     )))
	))

    (define-syntax define-auxiliary-syntaxes
      (syntax-rules ()
	((_ ?key)
	 (define-syntax ?key (syntax-rules ())))
	((_ ?key0 ?key1 . ?keys)
	 (begin
	   (define-auxiliary-syntaxes ?key0)
	   (define-auxiliary-syntaxes ?key1 . ?keys)))
	))

    (define-auxiliary-syntaxes token end-of-input)

    (define-syntax case-token
      (lambda (stx)
	(syntax-case stx (token end-of-input)
	  ((?ctx ?token-expr
		 ((token)        . ?token-object-body)
		 ((end-of-input) . ?end-of-input-body))
	   (with-syntax
	       ((SYNNER (datum->syntax #'?ctx 'synner))
		(TOKEN  (datum->syntax #'?ctx 'token)))
	     #'(let ((TOKEN ?token-expr))
		 (cond ((<token>?      TOKEN) . ?token-object-body)
		       ((end-of-input? TOKEN) . ?end-of-input-body)
		       (else
			(SYNNER "internal error: invalid object from lexer" TOKEN))))))
	  )))

    (define (syntax->list stx)
      (syntax-case stx ()
	(() '())
	((?car . ?cdr)
	 (cons #'?car (syntax->list #'?cdr)))))

;;; --------------------------------------------------------------------

    (define (atom-stx? stx)
      (atom? (syntax->datum stx)))

    (define (atom? obj)
      (or (number?     obj)
	  (boolean?    obj)
	  (char?       obj)
	  (string?     obj)
	  (bytevector? obj)
	  (null?       obj)))

    (define (flatten stx synner)
      ;;Given a syntax object STX representing an input expression: decompose it into
      ;;a flat  list of  raw tokens  and return the  list holding  the raw  tokens in
      ;;reverse  order.  We  expect the  list  to contain:  atoms as  defined by  the
      ;;function  ATOM?;   identifiers;  the   characters  open   parenthesis,  close
      ;;parenthesis and comma.
      ;;
      ;;We  have to  remember that  a  syntax object  can  be both  wrapper or  fully
      ;;unwrapped; this is relevant when we flatten syntax objects like:
      ;;
      ;;   (quote a)
      ;;   (begin a)
      ;;
      ;;which are meant to  be handled as atoms, not as lists.   For this reason this
      ;;function returns 2 values: the first is  a boolean, the second is an improper
      ;;list of raw tokens;  the boolean is true if the second return  value is to be
      ;;intepreted as an actual list of raw  tokens, false if it is to be interpreted
      ;;as an atom.
      ;;
      (syntax-case stx (begin quote quasiquote syntax quasisyntax unquote)
	(()
	 (values #f '()))
	((quote . ?stuff)
	 (values #f stx))
	((quasiquote . ?stuff)
	 (values #f stx))
	((syntax . ?stuff)
	 (values #f stx))
	((quasisyntax . ?stuff)
	 (values #f stx))
	((unquote . ?stuff)
	 (let-values (((unused result)
		       (flatten #'?stuff synner)))
	   (values #t (append result (list #\,)))))
	((begin . ?stuff)
	 (values #f stx))
	((?item ...)
	 (values #t
		 (cons #\)
		       (fold-left
			   (lambda (knil item)
			     (syntax-case item ()
			       ;;This clause  is needed to correctly  handle the case
			       ;;of   procedure   application  with   no   arguments.
			       ;;Examples:
			       ;;
			       ;;   (infix noargs())
			       ;;   (infix 2 + noargs() + 3)
			       ;;
			       ;;in which  the "()" must  be lexed as the  two tokens
			       ;;#\( and #\).
			       (()
				(append '(#\) #\() knil))
			       (_
				(let-values (((is-list? R)
					      (flatten item synner)))
				  (if is-list?
				      (append R knil)
				    (cons R knil))))
			       ))
			 (list #\()
			 (syntax->list #'(?item ...))))))
	(?id
	 (identifier? #'?id)
	 (values #f #'?id))
	(?atom
	 (atom-stx? #'?atom)
	 (values #f (syntax->datum #'?atom)))
	(_
	 (synner "invalid expression syntax" stx))))

;;; --------------------------------------------------------------------

    (define (tokenise obj synner)
      ;;Given a raw object from the flattened list of input tokens return an instance
      ;;of "<token>" describing it.
      ;;
      (cond ((identifier? obj)
	     (case (syntax->datum obj)
	       ((==)	EQUAL-TO-TOKEN)
	       ((!=)	NOT-EQUAL-TO-TOKEN)
	       ((<>)	NOT-EQUAL-TO-TOKEN)
	       ((≠)	NOT-EQUAL-TO-TOKEN)	;;Unicode symbol "\x2260;".
	       ((!)	BANG-TOKEN)
	       ((**)	EXPT-TOKEN)
	       ((%)	IMOD-TOKEN)
	       ((×)	MUL-TOKEN)		;;Unicode symbol "\xD7;".
	       ((⋅)	MUL-TOKEN)		;;Unicode symbol "\x22C5;".

	       ((&&)	AND-TOKEN)
	       ((⏐⏐)	OR-TOKEN)		;;Symbol "\x23D0;\x23D0;".
	       ((∧)	AND-TOKEN)		;;Unicode symbol "\x2227;".
	       ((∨)	OR-TOKEN)		;;Unicode symbol "\x2228;".
	       ((⊻)	XOR-TOKEN)		;;Unicode symbol "\x22BB;".
	       ((¬)	NOT-TOKEN)		;;Unicode symbol "\xAC;".

	       ((⏐)	BITWISE-IOR-TOKEN)	;;Unicode symbol "\x23D0;".
	       ((&)	BITWISE-AND-TOKEN)
	       ((^)	BITWISE-XOR-TOKEN)
	       ((~)	BITWISE-NOT-TOKEN)
	       ((<<)	BITWISE-SHIFT-LEFT-TOKEN)
	       ((>>)	BITWISE-SHIFT-RIGHT-TOKEN)

	       ((?)	QUESTION-MARK-TOKEN)
	       ((:)	COLON-TOKEN)
	       (else
		(case-identifiers obj
		  ((+)		PLUS-TOKEN)
		  ((-)		MINUS-TOKEN)
		  ((*)		MUL-TOKEN)
		  ((/)		DIV-TOKEN)
		  ((incr!)	INCR-TOKEN)
		  ((decr!)	DECR-TOKEN)
		  ((div)	IDIV-TOKEN)
		  ((mod)	IMOD-TOKEN)
		  ((div0)	IDIV0-TOKEN)
		  ((mod0)	IMOD0-TOKEN)
		  ((expt)	EXPT-TOKEN)
		  ((factorial)	FACTORIAL-TOKEN)

		  ((fx+)	FXPLUS-TOKEN)
		  ((fx-)	FXMINUS-TOKEN)
		  ((fx*)	FXMUL-TOKEN)
		  ((fxdiv)	FXDIV-TOKEN)
		  ((fxmod)	FXMOD-TOKEN)
		  ((fxdiv0)	FXDIV0-TOKEN)
		  ((fxmod0)	FXMOD0-TOKEN)

		  ((fl+)	FLPLUS-TOKEN)
		  ((fl-)	FLMINUS-TOKEN)
		  ((fl*)	FLMUL-TOKEN)
		  ((fl/)	FLDIV-TOKEN)
		  ((flexpt)	FLEXPT-TOKEN)

		  ((and)	AND-TOKEN)
		  ((or)		OR-TOKEN)
		  ((xor)	XOR-TOKEN)
		  ((not)	NOT-TOKEN)

		  ((<)		LESS-THAN-TOKEN)
		  ((>)		GREATER-THAN-TOKEN)
		  ((<=)		LESS-THAN-EQUAL-TO-TOKEN)
		  ((>=)		GREATER-THAN-EQUAL-TO-TOKEN)
		  ((=)		EQUAL-TO-TOKEN)

		  ((fx<?)	FXLESS-THAN-TOKEN)
		  ((fx>?)	FXGREATER-THAN-TOKEN)
		  ((fx<=?)	FXLESS-THAN-EQUAL-TO-TOKEN)
		  ((fx>=?)	FXGREATER-THAN-EQUAL-TO-TOKEN)
		  ((fx=?)	FXEQUAL-TO-TOKEN)

		  ((fl<?)	FLLESS-THAN-TOKEN)
		  ((fl>?)	FLGREATER-THAN-TOKEN)
		  ((fl<=?)	FLLESS-THAN-EQUAL-TO-TOKEN)
		  ((fl>=?)	FLGREATER-THAN-EQUAL-TO-TOKEN)
		  ((fl=?)	FLEQUAL-TO-TOKEN)

		  ((eq?)	EQ-PRED-TOKEN)
		  ((eqv?)	EQV-PRED-TOKEN)
		  ((equal?)	EQUAL-PRED-TOKEN)

		  ;; bitwise operators
		  ((bitwise-and)			BITWISE-AND-TOKEN)
		  ((bitwise-ior)			BITWISE-IOR-TOKEN)
		  ((bitwise-xor)			BITWISE-XOR-TOKEN)
		  ((bitwise-not)			BITWISE-NOT-TOKEN)
		  ((bitwise-arithmetic-shift-left)	BITWISE-SHIFT-LEFT-TOKEN)
		  ((bitwise-arithmetic-shift-right)	BITWISE-SHIFT-RIGHT-TOKEN)

		  ;; bitwise operators
		  ((fxand)				FXAND-TOKEN)
		  ((fxior)				FXIOR-TOKEN)
		  ((fxxor)				FXXOR-TOKEN)
		  ((fxnot)				FXNOT-TOKEN)
		  ((fxarithmetic-shift-left)		FXSHIFT-LEFT-TOKEN)
		  ((fxarithmetic-shift-right)		FXSHIFT-RIGHT-TOKEN)

		  (else
		   ;;It is a variable.
		   (make-<operand> obj))))))
	    ((char? obj)
	     (cond ((char=? obj #\()	LEFT-PAREN-TOKEN)
		   ((char=? obj #\))	RIGHT-PAREN-TOKEN)
		   ((char=? obj #\,)	COMMA-TOKEN)
		   (else
		    (synner "invalid character object from input" obj))))
	    (else
	     (make-<operand> obj))))

;;; --------------------------------------------------------------------

    (define (make-lexer token*)
      ;;Given a list of "<token>" records return a closure implementing the lexer.
      ;;
      ;;* When the lexer is called without arguments: it pops the next token from the
      ;;  list and returns it.
      ;;
      ;;* When the lexer is called with  a single argument: it returns the next token
      ;;  from the list without popping it.  The argument itself is ignored.
      ;;
      ;;* When there are no more tokens: the lexer returns the end-of-input object.
      ;;
      (assert (and (list? token*)
		   (for-all <token>? token*)))
      (case-lambda
       ((obj)	;peek
	(if (pair? token*)
	    (car token*)
	  (end-of-input-object)))
       (()	;get
	(if (pair? token*)
	    (receive-and-return (T)
		(car token*)
	      (set! token* (cdr token*)))
	  (end-of-input-object)))))

    (define-syntax-rule (end-of-input? ?object-from-lexer)
      (eof-object? ?object-from-lexer))

    (define-syntax-rule (end-of-input-object)
      (eof-object))

;;; --------------------------------------------------------------------

    (define (parse lexer synner caller-right-binding-power
		   immediate-end-of-input-handler)
      ;;This  procedure is  the  core of  the  Pratt parser.   It  composes the  next
      ;;sub-expression's  semantic value  parsing tokens  from the  lexer; it  can be
      ;;called by the operator's left-denotators to produce a right-hand argument.
      ;;
      ;;Let's examine  what happens when parsing the expression:
      ;;
      ;;   1 + 2 - 3
      ;;
      ;;which we represent with the sequence of tokens:
      ;;
      ;;   OPERAND[1] PLUS OPERAND[2] MINUS OPERAND[3]
      ;;
      ;;where PLUS and MINUS are operator  tokens.  We use the abbreviations: NUD for
      ;;token's null-denotator procedure; LED for token's left-denotator procedure.
      ;;
      ;;PARSE is called with minimum right-binding power:
      ;;
      ;;01.PARSE consumes the token OPERAND[1] and  calls its NUD, which just returns
      ;;the semantic value: fixnum 1.  PARSE tail-calls its sub-procedure LOOP.
      ;;
      ;;02.LOOP consumes the token PLUS, whose left-binding power is greater than the
      ;;minimum  right-binding power;  LOOP calls  the  LED of  PLUS with  1 as  left
      ;;semantic value.
      ;;
      ;;03.,,The LED of PLUS calls PARSE with its right-binding power.
      ;;
      ;;04.,,..PARSE  consumes the  token OPERAND[2]  and calls  its NUD,  which just
      ;;returns the semantic value: fixnum 2.  PARSE tail-calls LOOP.
      ;;
      ;;05.,,..LOOP looks ahead the token MINUS, whose left-binding power is equal to
      ;;the right-binding power or PLUS; LOOP returns the semantic value 2.
      ;;
      ;;06.,,The LED of PLUS composes the semantic value (#'+ 1 2) and returns it.
      ;;
      ;;07.LOOP consumes  the token MINUS,  whose left-binding power is  greater than
      ;;the minimum right-binding power;  LOOP calls the LED of MINUS  with (#'+ 1 2)
      ;;as left semantic value.
      ;;
      ;;08.,,The LED of MINUS calls PARSE with its right-binding power.
      ;;
      ;;09.,,..PARSE  consumes the  token OPERAND[3]  and calls  its NUD,  which just
      ;;returns the semantic value: fixnum 3.  PARSE tail-calls LOOP.
      ;;
      ;;10.,,..LOOP looks ahead the end-of-input and returns the semantic value 3.
      ;;
      ;;11.,,The LED  of MINUS  composes the  semantic value  (#'- (#'+  1 2)  3) and
      ;;returns it.
      ;;
      ;;12.LOOP looks ahead the end-of-input and returns the semantic value (#'- (#'+
      ;;1 2) 3).
      ;;
      (define (loop left-semantic-value lexer synner caller-right-binding-power)
	;;We have  acquired a semantic  value from  parsing previous tokens.   Now we
	;;loop parsing tokens  until a full sub-expression's semantic  value has been
	;;formed.
	;;
	;;While  the  left-binding power  of  the  next  token  is greater  than  the
	;;right-binding  power  of the  caller  denotator:  we continue  calling  the
	;;left-denotator of the next token.  It is this very mechanism that allows us
	;;to implement operator precedence, left and right associativity.
	;;
	(define-syntax-rule (recurse ?new-semantic-value)
	  (loop ?new-semantic-value lexer synner caller-right-binding-power))
	(case-token (lexer 'lookahead)
	  ((token)
	   ;;By using  FX>=? we make the  binary infix operators, with  the same left
	   ;;and right binding powers, left-associative by default; example:
	   ;;
	   ;;   (1 + 2 + 3) => (+ (+ 1 2) 3)
	   ;;
	   ;;by using FX>? they would have been right-associative by default.
	   (if (fx>=? caller-right-binding-power (<token>-left-binding-power token))
	       left-semantic-value
	     (begin
	       (lexer) ;consume the token
	       (recurse (call-led token lexer synner left-semantic-value)))))
	  ((end-of-input)
	   left-semantic-value)))

      ;;When correct input is  given: we expect at least a  sub-expression.  It is an
      ;;exception if we immediately find end-of-input.
      (case-token (lexer)
	((token)
	 (loop (call-nud token lexer synner)
	       lexer synner caller-right-binding-power))
	((end-of-input)
	 ;;We got an EOI before composing a full expression.
	 (immediate-end-of-input-handler))))

;;; --------------------------------------------------------------------

    (define-record-type <token>
      ;;This is the base type of tokens for Pratt parsing.
      ;;
      (fields (immutable semantic-value)
		;Scheme object representing  the semantic value of  this token.  This
		;object can be anything.

	      (immutable left-binding-power)
		;A  fixnum  representing  the   left-binding  power  of  this  token.
		;Operands must  have the  minimum left-binding power;  operators must
		;have  a   left-binding  power  which  defines   precedence;  passive
		;syntactic tokens must have minimum left-binding power.

	      (immutable null-denotator)
		;The null-denotator  closure object  (NUD).  It  is called  when this
		;token  does *not*  have  a left  semantic value  to  which it  might
		;left-bind, or it has already been decided that this token does *not*
		;left-bind to the left semantic  value.  This denotator is allowed to
		;select its right-binding power depending on which tokens come next.
		;
		;Both operands  and operators  might have a  NUD that  does something
		;(rather than raising a syntax error exception).
		;
		;A null-denotator has the following signature:
		;
		;   (nud ?this-token ?lexer ?synner)
		;
		;where:  ?THIS-TOKEN  is the  token  instance;  ?LEXER is  the  lexer
		;procedure; ?SYNNER is used to raise errors.

	      (immutable left-denotator))
		;The left-denotator  closure object  (LED).  It  is called  when this
		;token *does*  have a  left semantic  value and  it has  already been
		;decided that this  token *does* left-bind to it.   This denotator is
		;allowed to select its right-binding  power depending on which tokens
		;come next.
		;
		;A left-denotator has the following signature:
		;
		;   (led ?this-token ?lexer ?synner ?left-semantic-value)
		;
		;where:  ?THIS-TOKEN is  this  token instance;  ?LEXER  is the  lexer
		;procedure; ?SYNNER is used  to raise errors; ?LEFT-SEMANTIC-VALUE is
		;the semantic value composed by parsing previous tokens.
      (protocol
       (lambda (make-record)
	 (lambda (semantic-value left-binding-power null-denotator left-denotator)
	   (assert (fixnum?    left-binding-power))
	   (assert (procedure? null-denotator))
	   (assert (procedure? left-denotator))
	   (make-record semantic-value left-binding-power null-denotator left-denotator)))))

    (define-syntax-rule (call-nud ?token ?lexer ?synner)
      ;;Call the null-denotator procedure of ?TOKEN.
      ;;
      (let ((token ?token))
	((<token>-null-denotator token) token ?lexer ?synner)))

    (define-syntax-rule (call-led ?token ?lexer ?synner ?left-semantic-value)
      ;;Call the left-denotator procedure of ?TOKEN.
      ;;
      (let ((token ?token))
	((<token>-left-denotator token) token ?lexer ?synner ?left-semantic-value)))

;;; --------------------------------------------------------------------

    (define-record-type <operand>
      ;;This  is the  type of  operand tokens  for Pratt  parsing.  Conceptually,  an
      ;;operand  has both  left and  right  binding powers  set to  the minimum;  the
      ;;previous and next tokens  decide whether an operand will bind  to the left or
      ;;right.
      ;;
      (parent <token>)
      (protocol
       (lambda (make-token)
	 (lambda (semantic-value)
	   ((make-token semantic-value MINIMUM-BINDING-POWER <operand>-nud <operand>-led))))))

    (define (<operand>-nud this-token lexer synner)
      ;;The token is an operand and it starts a sequence of tokens which are meant to
      ;;compose  a sub-expression.   Return the  semantic  value and  let the  caller
      ;;decide if this  token binds to the  left or right; the caller  is usually the
      ;;PARSE procedure.
      ;;
      (<token>-semantic-value this-token))

    (define (<operand>-led this-token lexer synner left-semantic-value)
      (synner "operand found when an operator was expected" this-token))

;;; --------------------------------------------------------------------

    (define-record-type <operator>
      ;;This is the type  of operator tokens for Pratt parsing.   We decide that only
      ;;identifiers are operators.
      ;;
      (parent <token>)
      (protocol
       (lambda (make-token)
	 (lambda (id token-left-binding-power null-denotator left-denotator)
	   (identifier? id)
	   ((make-token id token-left-binding-power null-denotator left-denotator))))))

;;; --------------------------------------------------------------------

    (define-record-type <fixed-right-binding-power-operator>
      ;;Record type  of operators  of which  we know the  right-binding power  of the
      ;;null-denotator and  left-denotator procedures is  always the same,  no matter
      ;;which next tokens come out of the lexer.
      ;;
      (parent <operator>)
      (fields (immutable right-binding-power))
		;A  fixnum  representing  the  right-binding power  of  this  token's
		;null-denotator and left-denotator procedures.
      (protocol
       (lambda (make-operator)
	 (lambda (id token-left-binding-power nud/led-right-binding-power
		null-denotator left-denotator)
	   (assert (fixnum? nud/led-right-binding-power))
	   ((make-operator id token-left-binding-power null-denotator left-denotator)
	    nud/led-right-binding-power)))))

;;; --------------------------------------------------------------------

    (define-record-type <infix-operator>
      ;;This is the record type of binary infix operators.
      ;;
      (parent <fixed-right-binding-power-operator>)
      (protocol
       (lambda (make-fixed-right-binding-power-operator)
	 (lambda (id token-left-binding-power nud/led-right-binding-power)
	   ((make-fixed-right-binding-power-operator
	     id token-left-binding-power nud/led-right-binding-power
	     <infix-operator>-nud <infix-operator>-led))))))

    (define (<infix-operator>-nud this-token lexer synner)
      ;;This token is a binary infix operator  and it has *no* left semantic value it
      ;;might left-bind to: this is a syntax error.
      ;;
      (synner "binary infix operator without left operand" this-token))

    (define (<infix-operator>-led this-token lexer synner left-semantic-value)
      ;;This token is  a binary infix operator,  it has a left semantic  value and it
      ;;has already been decided that this token binds to it.
      ;;
      (define-constant THIS-DENOTATOR-RIGHT-BINDING-POWER
	(<fixed-right-binding-power-operator>-right-binding-power this-token))
      (define (immediate-end-of-input-handler)
        (synner "infix operator without right operand" this-token))
      (let* ((this-semantic-value (<token>-semantic-value this-token))
	     (right-semantic-value (parse lexer synner THIS-DENOTATOR-RIGHT-BINDING-POWER
					  immediate-end-of-input-handler)))
	(list this-semantic-value
	      left-semantic-value
	      right-semantic-value)))

;;; --------------------------------------------------------------------

    (define-record-type <left-assoc-infix-operator>
      ;;This is  the record type of  left-associative binary infix operators  like *.
      ;;To be left-associative the operator X must act as follows:
      ;;
      ;;   A x B x C => (x (x A B) C)
      ;;
      ;;the compared binding powers are the following:
      ;;
      ;;                       A x B x C
      ;;                         ^   ^
      ;;   LED right-binding power   token left-binding power
      ;;
      ;;and the LED right-binding power must be higher than or equal to the other.
      ;;
      (parent <infix-operator>)
      (protocol
       (lambda (make-infix-operator)
	 (lambda (id token-left-binding-power nud/led-right-binding-power)
	   (assert (fx<=? token-left-binding-power nud/led-right-binding-power))
	   ((make-infix-operator id token-left-binding-power
				 nud/led-right-binding-power))))))

;;; --------------------------------------------------------------------

    (define-record-type <right-assoc-infix-operator>
      ;;This  is the  record type  of right-associative  binary infix  operators like
      ;;EXPT.  To be right-associative the operator X must act as follows:
      ;;
      ;;   A x B x C => (x A (x B C))
      ;;
      ;;the compared binding powers are the following:
      ;;
      ;;                       A x B x C
      ;;                         ^   ^
      ;;   LED right-binding power   token left-binding power
      ;;
      ;;and the token left-binding power must be higher than the other.
      ;;
      (parent <infix-operator>)
      (protocol
       (lambda (make-infix-operator)
	 (lambda (id token-left-binding-power nud/led-right-binding-power)
	   (assert (fx>? token-left-binding-power nud/led-right-binding-power))
	   ((make-infix-operator id token-left-binding-power
				 nud/led-right-binding-power))))))

;;; --------------------------------------------------------------------

    (define-record-type <symmetric-left-assoc-infix-operator>
      ;;Record type of  left-associative binary infix operators of which  we know the
      ;;left-binding  power  of  the  token   and  the  right-binding  power  of  the
      ;;left-denotator procedure is always the same, no matter which next tokens come
      ;;out of the lexer.
      ;;
      ;;Examples are the common arithmetic operators  +, -, *, /, the logic operators
      ;;AND, OR, XOR,  NOT and the comparison  operators <, >, <=, >=,  =, !=; notice
      ;;that EXPT is right-associative, so it is not of this type.
      ;;
      (parent <left-assoc-infix-operator>)
      (protocol
       (lambda (make-left-assoc-infix-operator)
	 (lambda (id binding-power)
	   ((make-left-assoc-infix-operator id binding-power binding-power))))))

;;; --------------------------------------------------------------------

    (define-record-type <prefix-operator>
      ;;This is the record type of unary prefix operators like NOT.
      ;;
      (parent <fixed-right-binding-power-operator>)
      (protocol
       (lambda (make-fixed-right-binding-power-operator)
	 (lambda (id nud/led-right-binding-power)
	   ((make-fixed-right-binding-power-operator
	     id MINIMUM-BINDING-POWER nud/led-right-binding-power
	     <prefix-operator>-nud <prefix-operator>-led))))))

    (define (<prefix-operator>-nud this-token lexer synner)
      ;;This token is a unary prefix operator  and it has *no* left semantic value it
      ;;might left-bind to.
      ;;
      ;;The scenario of tokens from the lexer is this:
      ;;
      ;;   this-token next-token
      ;;
      ;;where NEXT-TOKEN is still in the lexer.
      ;;
      ;;Examples:
      ;;
      ;;* This token is the operator "not" in the following expression:
      ;;
      ;;     not 4
      ;;
      ;;  the next token  is "4".  The next token is an operand:  we just acquire the
      ;;  next token and call its left-denotator to obtain the full right operand.
      ;;
      ;;* This token is the leftmost operator "not" in the following expression:
      ;;
      ;;     not not 4
      ;;      ^
      ;;     this one
      ;;
      ;;  the next  token is "not".  The  next token is an operator:  we just acquire
      ;;   the next  token  and call  its  null-denotator to  obtain  the full  right
      ;;  operand.
      ;;
      (define-constant THIS-DENOTATOR-RIGHT-BINDING-POWER
	(<fixed-right-binding-power-operator>-right-binding-power this-token))
      (define (immediate-end-of-input-handler)
	(synner "unexpected end of input while parsing operand for unary prefix operator"
		this-token))
      (let ((this-semantic-value  (<token>-semantic-value this-token))
	    (right-semantic-value (parse lexer synner THIS-DENOTATOR-RIGHT-BINDING-POWER
					 immediate-end-of-input-handler)))
	(list this-semantic-value
	      right-semantic-value)))

    (define (<prefix-operator>-led this-token lexer synner left-semantic-value)
      ;;This token is  a unary prefix operator,  it has a left semantic  value and it
      ;;has already been decided that it left-binds to it: this is a syntax error.
      ;;
      (synner "unary prefix operator has no left operand" this-token))

;;; --------------------------------------------------------------------

    (define-record-type <postfix-operator>
      ;;This  is the  record  type of  unary  postfix operators  like  "!" (which  is
      ;;factorial).
      ;;
      (parent <fixed-right-binding-power-operator>)
      (protocol
       (lambda (make-fixed-right-binding-power-operator)
	 (lambda (id token-left-binding-power)
	   ((make-fixed-right-binding-power-operator
	     id token-left-binding-power MINIMUM-BINDING-POWER
	     <postfix-operator>-nud <postfix-operator>-led))))))

    (define (<postfix-operator>-nud this-token lexer synner)
      ;;This token is a unary postfix operator and it has *no* left semantic value it
      ;;might left-bind to: this is a syntax error.
      ;;
      (synner "unary postfix operator without left operand" this-token))

    (define (<postfix-operator>-led this-token lexer synner left-semantic-value)
      ;;This token is a  unary postfix operator, it has a left  semantic value and it
      ;;has already been been decided that it left-binds to it.
      ;;
      (list (<token>-semantic-value this-token) left-semantic-value))

;;; --------------------------------------------------------------------

    (define-record-type <left-assoc-infix/prefix-operator>
      ;;This is the  record type of operators  that can be used both  as binary infix
      ;;and unary prefix.  Examples are the arithmetic operators + and -.
      ;;
      (parent <fixed-right-binding-power-operator>)
      (protocol
       (lambda (make-fixed-right-binding-power-operator)
	 (lambda (id token-left-binding-power nud/led-right-binding-power)
	   ((make-fixed-right-binding-power-operator
	     id token-left-binding-power nud/led-right-binding-power
	     <prefix-operator>-nud <infix-operator>-led))))))

;;; --------------------------------------------------------------------

    (define-record-type <prefix/postfix-operator>
      ;;This is the base record type for operators that can appear in both prefix and
      ;;postfix position, for example the increment and decrement operators.
      ;;
      (parent <fixed-right-binding-power-operator>)
      (fields (immutable postfix-semantic-value))
		;A  semantic  value to  be  used  when  the  operator is  in  postfix
		;position.
      (protocol
       (lambda (make-fixed-right-binding-power-operator)
	 (lambda (prefix-id postfix-id token-left-binding-power nud/led-right-binding-power)
	   (assert (identifier? postfix-id))
	   ((make-fixed-right-binding-power-operator
	     prefix-id token-left-binding-power nud/led-right-binding-power
	     <prefix-operator>-nud <prefix/postfix-operator>-led)
	    postfix-id)))))

    (define (<prefix/postfix-operator>-led this-token lexer synner left-semantic-value)
      ;;This token is  a unary prefix/postfix operator, it has  a left semantic value
      ;;and it has already been been decided that it left-binds to it; this means the
      ;;operator is in postfix position.
      ;;
      (list (<prefix/postfix-operator>-postfix-semantic-value this-token)
	    left-semantic-value))

;;; --------------------------------------------------------------------

    (define-record-type <symmetric-prefix/postfix-operator>
      ;;This is  the record  type for operators  that can appear  in both  prefix and
      ;;postfix  position, for  example the  increment and  decrement operators,  for
      ;;which  we  know  the  token  left-binding  power  equals  the  left-denotator
      ;;right-binding power.
      ;;
      (parent <prefix/postfix-operator>)
      (protocol
       (lambda (make-prefix/postfix-operator)
	 (lambda (prefix-id postfix-id binding-power)
	   ((make-prefix/postfix-operator prefix-id postfix-id
					  binding-power binding-power))))))

;;; --------------------------------------------------------------------

    (define-record-type <passive-syntactic-token>
      ;;This is the base type of passive syntactic tokens.  These tokens are meant to
      ;;be consumed  by the NUD  or LED of  operators; the NUD  and LED of  a passive
      ;;token are never called when correct input is parsed.
      ;;
      (parent <token>)
      (fields (immutable description))
      (protocol
       (lambda (make-token)
	 (lambda (description)
	   ((make-token #f MINIMUM-BINDING-POWER
			<passive-syntactic-token>-nud
			<passive-syntactic-token>-led)
	    description)))))

    (define (<passive-syntactic-token>-syntax-error-message token)
      (string-append "unexpected " (<passive-syntactic-token>-description token)))

    (define (<passive-syntactic-token>-nud this-token lexer synner)
      (synner (<passive-syntactic-token>-syntax-error-message this-token)
	      this-token))

    (define (<passive-syntactic-token>-led this-token lexer synner left-semantic-value)
      (synner (<passive-syntactic-token>-syntax-error-message this-token)
	      this-token))

;;; --------------------------------------------------------------------

    (define-record-type <right-paren>
      ;;The right parenthesis is meant to be  passively consumed by the NUD or LED of
      ;;the left parenthesis.
      ;;
      (parent <passive-syntactic-token>)
      (protocol
       (lambda (make-passive-syntactic-token)
	 (let ((memoised #f))
	   (lambda ()
	     (or memoised
		 (receive-and-return (V)
		     ((make-passive-syntactic-token "right parenthesis"))
		   (set! memoised V))))))))

;;; --------------------------------------------------------------------

    (define-record-type <comma>
      ;;The comma separator is meant to be  passively consumed by the LED of the left
      ;;parenthesis.
      ;;
      (parent <passive-syntactic-token>)
      (protocol
       (lambda (make-passive-syntactic-token)
	 (let ((memoised #f))
	   (lambda ()
	     (or memoised
		 (receive-and-return (V)
		     ((make-passive-syntactic-token "comma separator"))
		   (set! memoised V))))))))

;;; --------------------------------------------------------------------

    (define-record-type <left-paren>
      ;;The left parenthesis is an operator.
      ;;
      (parent <fixed-right-binding-power-operator>)
      (protocol
       (lambda (make-fixed-right-binding-power-operator)
	 (let ((memoised #f))
	   (lambda ()
	     (or memoised
		 (receive-and-return (V)
		     ((make-fixed-right-binding-power-operator
		       #\(
		       LEFT-PAREN-LEFT-BINDING-POWER
		       LEFT-PAREN-RIGHT-BINDING-POWER
		       <left-paren>-nud <left-paren>-led))
		   (set! memoised V))))))))

    (define (<left-paren>-nud this-token lexer synner)
      ;;This token is a left parenthesis and there is no left semantic value it might
      ;;left-bind to.  Open a parenthetical sub-expression: read a sub-expression and
      ;;consume a right parenthesis token.
      ;;
      ;;Example, when this procedure is called the left-paren has just been consumed:
      ;;
      ;;   a * (b - c)
      ;;        ^
      ;;    we are here
      ;;
      (define-constant THIS-DENOTATOR-RIGHT-BINDING-POWER
	(<fixed-right-binding-power-operator>-right-binding-power this-token))
      (define (end-of-input-handler)
	(synner "end of input while looking for matching sub-expression right parenthesis"
		this-token))
      (let ((left-semantic-value (parse lexer synner
					THIS-DENOTATOR-RIGHT-BINDING-POWER
					end-of-input-handler)))
	(case-token (lexer)
	  ((token)
	   (if (<right-paren>? token)
	       left-semantic-value
	     (synner "expected matching right parenthesis" token)))
	  ((end-of-input)
	   (end-of-input-handler)))))

    (define (<left-paren>-led this-token lexer synner left-semantic-value)
      ;;This token is a  left parenthesis, there is a left semantic  value and it has
      ;;already been  decided that this  token left-binds to  it.  Start the  list of
      ;;arguments  for   a  procedure  application  sub-expression:   read  arguments
      ;;separated by comma  tokens and finally consume the  right parenthesis token.
      ;;
      ;;Example, when this procedure is called the left-paren has just been consumed:
      ;;
      ;;   func ( arg1 , arg , ... )
      ;;          ^
      ;;    we are here
      ;;
      ;;We expect the LEFT-SEMANTIC-VALUE to  represent an expression evaluating to a
      ;;procedure and the next tokens to form an arguments list.
      ;;
      ;;NOTE We  use the comma as  arguments separator; the Scheme  reader transforms
      ;;the sequence:
      ;;
      ;;   , ?form
      ;;
      ;;into:
      ;;
      ;;  (unsyntax ?form)
      ;;
      ;;so the list of arguments is:
      ;;
      ;;  ( arg1 (unsyntax arg) ... )
      ;;
      ;;NOTE R6RS does not define the comma to be a delimiter, so writing:
      ;;
      ;;   func (arg1, arg, ...)
      ;;
      ;;with no space between  the ARG and the comma is a syntax  error; it should be
      ;;trivial to change the Scheme reader to handle the comma as a delimiter.
      ;;
      (define-constant THIS-DENOTATOR-RIGHT-BINDING-POWER
	(<fixed-right-binding-power-operator>-right-binding-power this-token))

      (define (end-of-input-handler)
	(synner "unexpected end of input while reading list of procedure application arguments" this-token))

      (define (unexpected-token token)
	(synner "unexpected token while reading list of procedure application arguments" token))

      (define (loop reversed-list-of-arguments)
	(case-token (lexer 'lookahead)
	  ((token)
	   (cond ((<right-paren>? token)
		  (lexer) ;consume the token
		  ;;Return a semantic value representing a function application
		  ;;with arguments.
		  (cons left-semantic-value (reverse reversed-list-of-arguments)))
		 ((<comma>? token)
		  (lexer) ;consume the token
		  (let ((next-semantic-value (parse lexer synner
						    THIS-DENOTATOR-RIGHT-BINDING-POWER
						    end-of-input-handler)))
		    (loop (cons next-semantic-value reversed-list-of-arguments))))
		 (else
		  (unexpected-token token))))
	  ((end-of-input)
	   (end-of-input-handler))))

      ;;First we expect a closed parenthesis or an argument.
      (case-token (lexer 'lookahead)
	((token)
	 (if (<right-paren>? token)
	     (begin
	       (lexer) ;consume the token
	       ;;Return a semantic value representing a function application with
	       ;;no arguments.
	       (list left-semantic-value))
	   (loop (list (parse lexer synner THIS-DENOTATOR-RIGHT-BINDING-POWER
			      end-of-input-handler)))))
	((end-of-input)
	 (end-of-input-handler))))

;;; --------------------------------------------------------------------

    (define-record-type <colon>
      ;;The colon is the separator in the syntax:
      ;;
      ;;   ?test ? ?consequent : ?alternate
      ;;
      ;;it is meant  to be passively consumed by the  left-denotator procedure of the
      ;;question mark.
      ;;
      (parent <passive-syntactic-token>)
      (protocol
       (lambda (make-passive-syntactic-token)
	 (let ((memoised #f))
	   (lambda ()
	     (or memoised
		 (receive-and-return (V)
		     ((make-passive-syntactic-token "colon"))
		   (set! memoised V))))))))

;;; --------------------------------------------------------------------

    (define-record-type <question-mark>
      ;;The  question mark  is the  operator  in the  ternary conditional  expression
      ;;syntax:
      ;;
      ;;   ?test ? ?consequent : ?alternate
      ;;
      (parent <fixed-right-binding-power-operator>)
      (protocol
       (lambda (make-fixed-right-binding-power-operator)
	 (let ((memoised #f))
	   (lambda ()
	     (or memoised
		 (receive-and-return (V)
		     ((make-fixed-right-binding-power-operator
		       #\?
		       QUESTION-MARK-LEFT-BINDING-POWER
		       QUESTION-MARK-RIGHT-BINDING-POWER
		       <question-mark>-nud <question-mark>-led))
		   (set! memoised V))))))))

    (define (<question-mark>-nud this-token lexer synner)
      ;;This token is  a question mark and  there is no left semantic  value it might
      ;;left-bind to: this is a syntax error.
      ;;
      (synner "question mark operator without test operand" this-token))

    (define (<question-mark>-led this-token lexer synner left-semantic-value)
      ;;This token  is a question  mark, there  is a left  semantic value and  it has
      ;;already been decided that this token left-binds to it.
      ;;
      ;;We expect the LEFT-SEMANTIC-VALUE to  represent the test expression.  When we
      ;;enter this procedure the question mark has been already parsed:
      ;;
      ;;   ?test ? ?consequent : ?alternate
      ;;           ^
      ;;           we are here
      ;;
      ;;so  we  read  a  sub-expression  as consequent,  consume  the  colon  passive
      ;;syntactic token, and finally read a sub-expression as alternate.
      ;;
      (define-constant THIS-DENOTATOR-RIGHT-BINDING-POWER
	(<fixed-right-binding-power-operator>-right-binding-power this-token))

      (define (end-of-input-handler)
	(synner "unexpected end of input while reading ternary conditional expression" this-token))

      (define (unexpected-token token)
	(synner "unexpected token while reading ternary conditional expression" token))

      (let ((consequent (parse lexer synner THIS-DENOTATOR-RIGHT-BINDING-POWER
			       end-of-input-handler)))
	(case-token (lexer)
	  ((token)
	   (if (<colon>? token)
	       (let ((alternate (parse lexer synner THIS-DENOTATOR-RIGHT-BINDING-POWER
				       end-of-input-handler)))
		 #`(if #,left-semantic-value
		       #,consequent
		     #,alternate))
	     (unexpected-token token)))
	  ((end-of-input)
	   (end-of-input-handler)))))

;;; --------------------------------------------------------------------

    ;;The fixnum  zero can be used  as minimum binding  power (but such value  is not
    ;;enforced as minimum, negative fixnums will work just fine).
    (define-constant MINIMUM-BINDING-POWER		0)
    (define-constant INFIX-LOGIC-BINDING-POWER		300)
    (define-constant PREFIX-LOGIC-BINDING-POWER		350)
    (define-constant COMPARISON-BINDING-POWER		400)
    (define-constant PLUS/MINUS-BINDING-POWER		500)
    (define-constant MUL/DIV-BINDING-POWER		600)
    (define-constant MOD-BINDING-POWER			650)
    (define-constant EXPT-RIGHT-BINDING-POWER		700)
    (define-constant EXPT-LEFT-BINDING-POWER		800)
    (define-constant FACTORIAL-LEFT-BINDING-POWER	900)
    (define-constant INCR/DECR-BINDING-POWER		1000)
    (define-constant INFIX-BITWISE-BINDING-POWER	1300)
    (define-constant PREFIX-BITWISE-BINDING-POWER	1350)
    (define-constant INFIX-BITSHIFT-BINDING-POWER	1400)
    (define-constant LEFT-PAREN-LEFT-BINDING-POWER	2000)
    (define-constant LEFT-PAREN-RIGHT-BINDING-POWER	MINIMUM-BINDING-POWER)

    (define-constant QUESTION-MARK-LEFT-BINDING-POWER	400)
    (define-constant QUESTION-MARK-RIGHT-BINDING-POWER	MINIMUM-BINDING-POWER)

;;; --------------------------------------------------------------------

    (define-constant PLUS-TOKEN
      (make-<left-assoc-infix/prefix-operator> #'+ PLUS/MINUS-BINDING-POWER PLUS/MINUS-BINDING-POWER))

    (define-constant MINUS-TOKEN
      (make-<left-assoc-infix/prefix-operator> #'- PLUS/MINUS-BINDING-POWER PLUS/MINUS-BINDING-POWER))

    (define-constant MUL-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'* MUL/DIV-BINDING-POWER))

    (define-constant DIV-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'/ MUL/DIV-BINDING-POWER))

    (define-constant IDIV-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'div MUL/DIV-BINDING-POWER))

    (define-constant IMOD-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'mod MOD-BINDING-POWER))

    (define-constant IDIV0-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'div0 MUL/DIV-BINDING-POWER))

    (define-constant IMOD0-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'mod0 MOD-BINDING-POWER))

    (define-constant FACTORIAL-TOKEN
      (make-<postfix-operator> #'factorial FACTORIAL-LEFT-BINDING-POWER))

    (define-constant BANG-TOKEN
      (make-<prefix/postfix-operator> #'not #'factorial FACTORIAL-LEFT-BINDING-POWER PREFIX-LOGIC-BINDING-POWER))

    (define-constant EXPT-TOKEN
      (make-<right-assoc-infix-operator> #'expt EXPT-LEFT-BINDING-POWER EXPT-RIGHT-BINDING-POWER))

    (define-constant INCR-TOKEN
      (make-<symmetric-prefix/postfix-operator> #'pre-incr #'post-incr INCR/DECR-BINDING-POWER))

    (define-constant DECR-TOKEN
      (make-<symmetric-prefix/postfix-operator> #'pre-decr #'post-decr INCR/DECR-BINDING-POWER))

;;; --------------------------------------------------------------------

    (define-constant FXPLUS-TOKEN
      (make-<left-assoc-infix/prefix-operator> #'fx+ PLUS/MINUS-BINDING-POWER PLUS/MINUS-BINDING-POWER))

    (define-constant FXMINUS-TOKEN
      (make-<left-assoc-infix/prefix-operator> #'fx- PLUS/MINUS-BINDING-POWER PLUS/MINUS-BINDING-POWER))

    (define-constant FXMUL-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fx* MUL/DIV-BINDING-POWER))

    (define-constant FXDIV-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fxdiv MUL/DIV-BINDING-POWER))

    (define-constant FXMOD-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fxmod MOD-BINDING-POWER))

    (define-constant FXDIV0-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fxdiv0 MUL/DIV-BINDING-POWER))

    (define-constant FXMOD0-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fxmod0 MOD-BINDING-POWER))

;;; --------------------------------------------------------------------

    (define-constant FLPLUS-TOKEN
      (make-<left-assoc-infix/prefix-operator> #'fl+ PLUS/MINUS-BINDING-POWER PLUS/MINUS-BINDING-POWER))

    (define-constant FLMINUS-TOKEN
      (make-<left-assoc-infix/prefix-operator> #'fl- PLUS/MINUS-BINDING-POWER PLUS/MINUS-BINDING-POWER))

    (define-constant FLMUL-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fl* MUL/DIV-BINDING-POWER))

    (define-constant FLDIV-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fl/ MUL/DIV-BINDING-POWER))

    (define-constant FLEXPT-TOKEN
      (make-<right-assoc-infix-operator> #'flexpt EXPT-LEFT-BINDING-POWER EXPT-RIGHT-BINDING-POWER))

;;; --------------------------------------------------------------------

    (define-constant AND-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'and INFIX-LOGIC-BINDING-POWER))

    (define-constant OR-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'or INFIX-LOGIC-BINDING-POWER))

    (define-constant XOR-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'xor INFIX-LOGIC-BINDING-POWER))

    (define-constant NOT-TOKEN
      (make-<prefix-operator> #'not PREFIX-LOGIC-BINDING-POWER))

;;; --------------------------------------------------------------------

    (define-constant LESS-THAN-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'< COMPARISON-BINDING-POWER))

    (define-constant GREATER-THAN-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'> COMPARISON-BINDING-POWER))

    (define-constant LESS-THAN-EQUAL-TO-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'<= COMPARISON-BINDING-POWER))

    (define-constant GREATER-THAN-EQUAL-TO-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'>= COMPARISON-BINDING-POWER))

    (define-constant EQUAL-TO-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'= COMPARISON-BINDING-POWER))

    (define-constant NOT-EQUAL-TO-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'!= COMPARISON-BINDING-POWER))

;;; --------------------------------------------------------------------

    (define-constant FXLESS-THAN-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fx<? COMPARISON-BINDING-POWER))

    (define-constant FXGREATER-THAN-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fx>? COMPARISON-BINDING-POWER))

    (define-constant FXLESS-THAN-EQUAL-TO-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fx<=? COMPARISON-BINDING-POWER))

    (define-constant FXGREATER-THAN-EQUAL-TO-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fx>=? COMPARISON-BINDING-POWER))

    (define-constant FXEQUAL-TO-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fx=? COMPARISON-BINDING-POWER))

;;; --------------------------------------------------------------------

    (define-constant FLLESS-THAN-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fl<? COMPARISON-BINDING-POWER))

    (define-constant FLGREATER-THAN-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fl>? COMPARISON-BINDING-POWER))

    (define-constant FLLESS-THAN-EQUAL-TO-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fl<=? COMPARISON-BINDING-POWER))

    (define-constant FLGREATER-THAN-EQUAL-TO-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fl>=? COMPARISON-BINDING-POWER))

    (define-constant FLEQUAL-TO-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fl=? COMPARISON-BINDING-POWER))

;;; --------------------------------------------------------------------

    (define-constant EQ-PRED-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'eq? COMPARISON-BINDING-POWER))

    (define-constant EQV-PRED-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'eqv? COMPARISON-BINDING-POWER))

    (define-constant EQUAL-PRED-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'equal? COMPARISON-BINDING-POWER))

    (define-constant BITWISE-AND-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'bitwise-and INFIX-BITWISE-BINDING-POWER))

;;; --------------------------------------------------------------------

    (define-constant BITWISE-IOR-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'bitwise-ior INFIX-BITWISE-BINDING-POWER))

    (define-constant BITWISE-XOR-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'bitwise-xor INFIX-BITWISE-BINDING-POWER))

    (define-constant BITWISE-NOT-TOKEN
      (make-<prefix-operator> #'bitwise-not PREFIX-BITWISE-BINDING-POWER))

    (define-constant BITWISE-SHIFT-LEFT-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'bitwise-arithmetic-shift-left INFIX-BITSHIFT-BINDING-POWER))

    (define-constant BITWISE-SHIFT-RIGHT-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'bitwise-arithmetic-shift-right INFIX-BITSHIFT-BINDING-POWER))

;;; --------------------------------------------------------------------

    (define-constant FXAND-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fxand INFIX-BITWISE-BINDING-POWER))

    (define-constant FXIOR-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fxior INFIX-BITWISE-BINDING-POWER))

    (define-constant FXXOR-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fxxor INFIX-BITWISE-BINDING-POWER))

    (define-constant FXNOT-TOKEN
      (make-<prefix-operator> #'fxnot PREFIX-BITWISE-BINDING-POWER))

    (define-constant FXSHIFT-LEFT-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fxarithmetic-shift-left INFIX-BITSHIFT-BINDING-POWER))

    (define-constant FXSHIFT-RIGHT-TOKEN
      (make-<symmetric-left-assoc-infix-operator> #'fxarithmetic-shift-right INFIX-BITSHIFT-BINDING-POWER))

;;; --------------------------------------------------------------------

    (define-constant LEFT-PAREN-TOKEN
      (make-<left-paren>))

    (define-constant RIGHT-PAREN-TOKEN
      (make-<right-paren>))

    (define-constant COMMA-TOKEN
      (make-<comma>))

    (define-constant QUESTION-MARK-TOKEN
      (make-<question-mark>))

    (define-constant COLON-TOKEN
      (make-<colon>))

;;; --------------------------------------------------------------------

    (lambda (stx)
      (define (synner message subform)
    	(syntax-violation 'infix message stx subform))
      (define (immediate-end-of-input-handler)
	;;Special case: no input tokens.
	#'(values))
      (syntax-case stx ()
      	((_ . ?tokens)
	 (let-values (((unused obj*) (flatten #'?tokens synner)))
	   (let* ((obj*   (reverse obj*))
		  (token* (map (lambda (obj)
				 (tokenise obj synner))
			    obj*))
		  (lexer  (make-lexer token*))
		  (expr   (parse lexer synner MINIMUM-BINDING-POWER
				 immediate-end-of-input-handler)))
	     expr)))
      	))))


;;;; done

)

;;; end of file
;; Local Variables:
;; coding: utf-8-unix
;; fill-column: 85
;; eval: (put 'case-token 'scheme-indent-function 1)
;; End:
