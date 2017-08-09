;;;
;;;Part of: Infix
;;;Contents: testing infrastructure
;;;Date: Sun May 18, 2014
;;;
;;;Abstract
;;;
;;;
;;;
;;;Copyright (C) 2014, 2017 Marco Maggi <marco.maggi-ipsu@poste.it>
;;;
;;;This program is free software:  you can redistribute it and/or modify
;;;it under the terms of the  GNU General Public License as published by
;;;the Free Software Foundation, either version 3 of the License, or (at
;;;your option) any later version.
;;;
;;;This program is  distributed in the hope that it  will be useful, but
;;;WITHOUT  ANY   WARRANTY;  without   even  the  implied   warranty  of
;;;MERCHANTABILITY or  FITNESS FOR  A PARTICULAR  PURPOSE.  See  the GNU
;;;General Public License for more details.
;;;
;;;You should  have received a  copy of  the GNU General  Public License
;;;along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;;


#!r6rs
(library (checks)
  (export check check-report)
  (import (rnrs (6)))


;;;; testing infrastructure

(define check-count		0)
(define check-success-count	0)
(define check-failure-count	0)

(define (incr-check-count)
  (set! check-count (+ 1 check-count)))

(define (incr-success-count)
  (set! check-success-count (+ 1 check-success-count)))

(define (incr-success-failure)
  (set! check-failure-count (+ 1 check-failure-count)))

(define-syntax check
  (syntax-rules (=>)
    ((_ ?expr => ?expected-result)
     (check ?expr (=> equal?) ?expected-result))
    ((_ ?expr (=> ?equal) ?expected-result)
     (let ((result	?expr)
	   (expected	?expected-result))
       (incr-check-count)
       (if (?equal result expected)
	   (incr-success-count)
	 (begin
	   (incr-success-failure)
	   (display "test error, expected\n\n")
	   (write expected)
	   (newline)
	   (display "\ngot:\n\n")
	   (write result)
	   (newline)
	   (display "\ntest body:\n\n")
	   (write '(check ?expr (=> ?equal) ?expected-result))
	   (newline)
	   (flush-output-port (current-output-port))))))
    ))

(define (check-report)
  (display (string-append "*** executed " (number->string check-count)
			  " tests, successful: " (number->string check-success-count)
			  ", failed: "(number->string check-failure-count) "\n"))
  (flush-output-port (current-output-port)))


;;;; done

)

;;; end of file
;; Local Variables:
;; coding: utf-8-unix
;; End:
