; Copyright (c) 1990-1997 The MITRE Corporation
; 
; Authors: W. M. Farmer, J. D. Guttman, F. J. Thayer
;   
; The MITRE Corporation (MITRE) provides this software to you without
; charge to use, copy, modify or enhance for any legitimate purpose
; provided you reproduce MITRE's copyright notice in any copy or
; derivative work of this software.
; 
; This software is the copyright work of MITRE.  No ownership or other
; proprietary interest in this software is granted you other than what
; is granted in this license.
; 
; Any modification or enhancement of this software must identify the
; part of this software that was modified, by whom and when, and must
; inherit this license including its warranty disclaimers.
; 
; MITRE IS PROVIDING THE PRODUCT "AS IS" AND MAKES NO WARRANTY, EXPRESS
; OR IMPLIED, AS TO THE ACCURACY, CAPABILITY, EFFICIENCY OR FUNCTIONING
; OF THIS SOFTWARE AND DOCUMENTATION.  IN NO EVENT WILL MITRE BE LIABLE
; FOR ANY GENERAL, CONSEQUENTIAL, INDIRECT, INCIDENTAL, EXEMPLARY OR
; SPECIAL DAMAGES, EVEN IF MITRE HAS BEEN ADVISED OF THE POSSIBILITY OF
; SUCH DAMAGES.
; 
; You, at your expense, hereby indemnify and hold harmless MITRE, its
; Board of Trustees, officers, agents and employees, from any and all
; liability or damages to third parties, including attorneys' fees,
; court costs, and other related costs and expenses, arising out of your
; use of this software irrespective of the cause of said liability.
; 
; The export from the United States or the subsequent reexport of this
; software is subject to compliance with United States export control
; and munitions control restrictions.  You agree that in the event you
; seek to export this software or any derivative work thereof, you
; assume full responsibility for obtaining all necessary export licenses
; and approvals and for assuring compliance with applicable reexport
; restrictions.
; 
; Emulation of TEA in Common Lisp for IMPS: Author F. J. Thayer.
; 
; 
; COPYRIGHT NOTICE INSERTED: Wed Mar  5 13:36:30 EST 1997

(defun convert-to-string (l)
  (mapcar #'(lambda (x) (cons (car x) (symbol-name (cadr x))))
	  l))

(setq conversion-alist
      (convert-to-string
       '(
	 (list list)
	 (cons cons)
	 (+ +)
	 (1+ 1+)
	 (* *)
	 (- -)
	 (subtract -)
	 (/ /)
	 (< <)
	 (less? <)
	 (greater? >)
	 (> >)
	 (= =)
	 (<= <=)
	 (>= >=)
	 (abs abs)
	 (expt expt)
	 (mod mod)
	 (max max)
	 (min min)
	 (even? evenp)
	 (odd? oddp)
	 (positive? plusp)
	 (negative? minusp)
	 (=0? zerop)
	 (zero? zerop)
	 (not-greater? <=)
	 (not-less? >=)
	 (1+ 1+)
	 (-1+ 1-)
	 (subtract1 1-)
	 (gcd gcd)
	 (numerator numerator)
	 (denominator denominator)
	 (logand logand)
	 (logxor logxor)
	 (logior logior)
	 (length length)
	 (make-string make-string)
	 (car car)
	 (cdr cdr)
 
	 (cadr cadr)
	 (cdar cdar)
	 (cddr cddr)
	 (caar caar)
 
	 (caddr caddr)
	 (caadr caadr)
	 (caaar caaar)
	 (cadar cadar)
	 (cdddr cdddr)
	 (cdadr cdadr)
	 (cdaar cdaar)
	 (cddar cddar)

	 (caaddr caaddr)
	 (caaadr caaadr)
	 (caaaar caaaar)
	 (caadar caadar)
	 (cadddr cadddr)
	 (cadadr cadadr)
	 (cadaar cadaar)
	 (caddar caddar)

	 (cdaddr cdaddr)
	 (cdaadr cdaadr)
	 (cdaaar cdaaar)
	 (cdadar cdadar)
	 (cddddr cddddr)
	 (cddadr cddadr)
	 (cddaar cddaar)
	 (cdddar cdddar)

	 (char= char=)
	 (char<= char<=)
	 (char>= char>=)
	 (char< char<)
	 (char> char>)

	 ;;The following list was obtained as follows:
	 ;;gawk '/^\(setf-value-and-function/ { print $2, $4 > "fuba"} ' supplements.lisp


	 (generate-symbol gensym)
	 (string->symbol intern)
	 (symbol->string symbol-name)
	 (string-downcase string-downcase)
	 (string-downcase! string-downcase)
	 (string-elt elt)
	 (atom? atom)
	 (pair? consp)
	 (list? listp)
	 (null? null)
	 (copy-list copy-list)
	 (procedure? is-callable-thing)
	 (number? numberp)
	 (integer? integerp)
	 (rational? rationalp)
	 (symbol? symbolp)
					;   (>=0? tea::not-negative?)
					;   (<=0? tea::not-positive?)
	 (char? characterp)
	 (digit? digit-char-p)
	 (uppercase? upper-case-p)
	 (lowercase? lower-case-p)
	 (alphabetic? alpha-char-p)
	 (remainder rem)
	 (string? stringp)
	 (string-equal? string=)
	 (substring? search)
	 (string-length length)
	 (string-less? string<)
	 (reverse! nreverse)
	 (append! nconc)
	 (append append)
	 (reverse reverse)
	 (reduce reduce)
	 (posq position)
	 (lastcdr last)
	 (last last)
	 (cons* list*)
	 (memq member)
	 (memq? member)
	 ;; (mem tea::mem?)
	 (delq remove)
	 (delq! delete)
	 (assq assoc)
	 (vector-length length)
	 (eq? eq)
	 (equiv? eql)
	 (equal? equal)
	 (char->ascii char-code)
	 (ascii->char code-char)
	 (sort sort)
	 (sort-list! sort)
	 ;; (hash-< hash-order)
	 (string-hash sxhash)
	 (symbol-hash sxhash)
	 (descriptor-hash sxhash)
	 (eval eval)
	 (retrieve-y-or-n-from-user yes-or-no-p)
	 (quit bye)
	 (false? null)
	 (ashl ash)
	 (fixnum-ashl ash)
	 (->float float)
	 (float? floatp)

	 (fx+ +)
	 (fx- -)
	 (fx* *)
	 (fx= =)
	 (fx< <)
	 (fx<= <=)
	 (fx> >)
	 (fx>= >=)
	 (fixnum-logand logand)
	 (fixnum-logior logior)
	 (fixnum-lognot lognot)


	 )))
