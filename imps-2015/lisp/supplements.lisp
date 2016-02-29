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


(in-package "TEA-IMPLEMENTATION")

;;Basic symbols:
(eval-when (eval compile load)

(defmacro defmacro-synonym (sym-0 sym-1)
  (let ((restarg (generate-symbol)))
  `(progn
     (proclaim '(special ,sym-0))
     (setf (symbol-value ',sym-0) (symbol-function ',sym-1))
     (defmacro ,sym-0 (&rest ,restarg) (list* ',sym-1 ,restarg)))))


(defun setf-value-and-function (var fn)
  (proclaim (list 'special var))
  (setf (symbol-function var) fn)
  (setf (symbol-value var) fn)
  var)

;;;(defmacro setf-value-and-function (var fn)
;;;  '(progn
;;;     (setf (symbol-function ',var) ,fn)
;;;     (setf (symbol-value ',var) ,fn)
;;;     var))
  
(defun setf-value-from-function (var)
  (proclaim (list 'special var))
  (setf (symbol-value var) (symbol-function var)))

(defmacro copy-setf-method (new-fn old-fn lambda-list)
  (let ((store-value (generate-symbol)))
    `(%defsetf ,new-fn ,lambda-list (,store-value)
	       (list 'setf (list ',old-fn ,@lambda-list) ,store-value))))

(defmacro-synonym tea::list list)
(defmacro-synonym tea::cons cons)
(defmacro-synonym tea::+ +)
(defmacro-synonym tea::* *)
(defmacro-synonym tea::- -)
(defmacro-synonym tea::subtract -)
(defmacro-synonym tea::/ /)
(defmacro-synonym tea::< <)
(defmacro-synonym tea::less? <)
(defmacro-synonym tea::greater? >)
(defmacro-synonym tea::> >)
(defmacro-synonym tea::= =)
(defmacro-synonym tea::<= <=)
(defmacro-synonym tea::>= >=)
(defmacro-synonym tea::quotient floor)
(defmacro-synonym tea::abs abs)
(defmacro-synonym tea::expt expt)
(defmacro-synonym tea::mod mod)
(defmacro-synonym tea::max max)
(defmacro-synonym tea::min min)
(defmacro-synonym tea::even? evenp)
(defmacro-synonym tea::odd? oddp)
(defmacro-synonym tea::positive? plusp)
(defmacro-synonym tea::negative? minusp)
(defmacro-synonym tea::=0? zerop)
(defmacro-synonym tea::>0? plusp)
(defmacro-synonym tea::zero? zerop)
(defmacro-synonym tea::not-greater? <=)
(defmacro-synonym tea::not-less? >=)
(defmacro-synonym tea::1+ 1+)
(defmacro-synonym tea::-1+ 1-)
(defmacro-synonym tea::subtract1 1-)
(defmacro-synonym tea::lcm lcm)
(defmacro-synonym tea::gcd gcd)
(defmacro-synonym tea::numerator numerator)
(defmacro-synonym tea::denominator denominator)
(defmacro-synonym tea::remainder rem)

(defmacro-synonym tea::logand logand)
(defmacro-synonym tea::logxor logxor)
(defmacro-synonym tea::logior logior)
(defmacro-synonym tea::lognot lognot)
(defmacro-synonym tea::length length)
(defmacro-synonym tea::make-string make-string)

;;Equality Predicates
;(defmacro-synonym tea::eq? eq)
(defmacro-synonym tea::eq? eql)
(defmacro-synonym tea::equiv? eql)
(defmacro-synonym tea::equal? equal)

(defmacro-synonym tea::car car)
(defmacro-synonym tea::cdr cdr)

(defmacro-synonym tea::cadr cadr)
(defmacro-synonym tea::cdar cdar)
(defmacro-synonym tea::cddr cddr)
(defmacro-synonym tea::caar caar)

(defmacro-synonym tea::caddr caddr)
(defmacro-synonym tea::caadr caadr)
(defmacro-synonym tea::caaar caaar)
(defmacro-synonym tea::cadar cadar)
(defmacro-synonym tea::cdddr cdddr)
(defmacro-synonym tea::cdadr cdadr)
(defmacro-synonym tea::cdaar cdaar)
(defmacro-synonym tea::cddar cddar)

(defmacro-synonym tea::caaddr caaddr)
(defmacro-synonym tea::caaadr caaadr)
(defmacro-synonym tea::caaaar caaaar)
(defmacro-synonym tea::caadar caadar)
(defmacro-synonym tea::cadddr cadddr)
(defmacro-synonym tea::cadadr cadadr)
(defmacro-synonym tea::cadaar cadaar)
(defmacro-synonym tea::caddar caddar)

(defmacro-synonym tea::cdaddr cdaddr)
(defmacro-synonym tea::cdaadr cdaadr)
(defmacro-synonym tea::cdaaar cdaaar)
(defmacro-synonym tea::cdadar cdadar)
(defmacro-synonym tea::cddddr cddddr)
(defmacro-synonym tea::cddadr cddadr)
(defmacro-synonym tea::cddaar cddaar)
(defmacro-synonym tea::cdddar cdddar)

(defmacro-synonym tea::char= char=)
(defmacro-synonym tea::char<= char<=)
(defmacro-synonym tea::char>= char>=)
(defmacro-synonym tea::char< char<)
(defmacro-synonym tea::char> char>)


(copy-setf-method tea::car car (x))
(copy-setf-method tea::cdr cdr (x))

(copy-setf-method tea::cadr cadr (x))
(copy-setf-method tea::cdar cdar (x))
(copy-setf-method tea::cddr cddr (x))
(copy-setf-method tea::caar caar (x))

(copy-setf-method tea::caddr caddr (x))
(copy-setf-method tea::caadr caadr (x))
(copy-setf-method tea::caaar caaar (x))
(copy-setf-method tea::cadar cadar (x))
(copy-setf-method tea::cdddr cdddr (x))
(copy-setf-method tea::cdadr cdadr (x))
(copy-setf-method tea::cdaar cdaar (x))
(copy-setf-method tea::cddar cddar (x))

(copy-setf-method tea::caaddr caaddr (x))
(copy-setf-method tea::caaadr caaadr (x))
(copy-setf-method tea::caaaar caaaar (x))
(copy-setf-method tea::caadar caadar (x))
(copy-setf-method tea::cadddr cadddr (x))
(copy-setf-method tea::cadadr cadadr (x))
(copy-setf-method tea::cadaar cadaar (x))
(copy-setf-method tea::caddar caddar (x))

(copy-setf-method tea::cdaddr cdaddr (x))
(copy-setf-method tea::cdaadr cdaadr (x))
(copy-setf-method tea::cdaaar cdaaar (x))
(copy-setf-method tea::cdadar cdadar (x))
(copy-setf-method tea::cddddr cddddr (x))
(copy-setf-method tea::cddadr cddadr (x))
(copy-setf-method tea::cddaar cddaar (x))
(copy-setf-method tea::cdddar cdddar (x))

;;This symbol is exported to tea

(defun concatenate-symbol (&rest args)
  (intern 
   (apply #'concatenate 'string 
	  (mapcar #'(lambda (x) (cond ((symbolp x) (symbol-name x))
				      ((stringp x) x)
				      (t (format nil  "~A" x))))
		  args))))
(setf-value-from-function 'concatenate-symbol)

(defmacro-synonym tea::generate-symbol generate-symbol)

(defmacro-synonym tea::string->symbol intern)
(defmacro-synonym tea::symbol->string symbol-name)
(defmacro-synonym tea::string-downcase string-downcase)
(defmacro-synonym tea::string-downcase! string-downcase)

(defun tea::substring (str start count)
  (subseq str start (+ start count)))
(setf-value-from-function 'tea::substring)
(defmacro-synonym tea::string-elt elt)

(defun tea::always (value)
  (function (lambda (&rest args) (declare (ignore args)) value)))
(setf-value-from-function 'tea::always)

(defun tea::identity (x) x)
(setf-value-from-function 'tea::identity)

(defun tea::enforce (predicate value)
  (if (funcall (closure predicate) value) 
      value
    (tea::error "(enforce ~A ~A) failed" predicate value)))
(setf-value-from-function 'tea::enforce)

(defmacro-synonym tea::atom? atom)
(defmacro-synonym tea::pair? consp)
(defmacro-synonym tea::list? listp)
(defmacro-synonym tea::null? null)
(defmacro-synonym tea::copy-list copy-list)

(defun is-callable-thing (thing)
  (or (functionp thing) 
      (and (object? thing) (object-closure thing))))

(defmacro-synonym tea::procedure? is-callable-thing)
(defmacro-synonym tea::number? numberp)
(defmacro-synonym tea::integer? integerp)
(defmacro-synonym tea::rational? rationalp)
(defmacro-synonym tea::symbol? symbolp)
(defun tea::proper-list? (l)
  (or (null l)
      (and (consp l) (null (cdr (last l))))))
(setf-value-from-function 'tea::proper-list?)

(defmacro tea::not-negative? (x)
  `(<= 0 ,x))

(defmacro tea::not-positive? (x)
  `(<= ,x 0))

(defmacro tea::>=0? (x)
   `(<= 0 ,x))

(defmacro tea::<=0? (x)
   `(<= 0 ,x))

(defmacro-synonym tea::char? characterp)
(defmacro-synonym tea::digit? digit-char-p)
(defmacro-synonym tea::uppercase? upper-case-p)
(defmacro-synonym tea::lowercase? lower-case-p)
(defmacro-synonym tea::alphabetic? alpha-char-p)
(defun tea::whitespace? (char)
  (member (char-code char) '(9 10 11 12 13 32 )  :test #'=))
(setf-value-from-function 'tea::whitespace?)

;;strings

(defmacro-synonym tea::string? stringp)
(defmacro-synonym tea::string-equal? string=)
(defmacro-synonym tea::substring? search)
(defmacro-synonym tea::string-length length)
(defmacro tea::string-empty? (str) `(= (length ,str) 0))


;;Should have been more consistently called string-blank?

(defun tea::blank? (str)
  (every #'tea::whitespace? str))
(setf-value-from-function 'tea::blank?)

(defun tea::prefix? (str1 str2)
  (let ((s (search str1 str2)))
    (and s (= s 0))))

;;(proclaim '(inline  tea::string-append))
(defun tea::string-append (&rest args)
  (apply #'concatenate 'string args))
(setf-value-from-function 'tea::string-append)

(defmacro-synonym tea::string-less? string<)

(defmacro tea::string-tail (l)
  `(subseq ,l 1))

(defun tea::separated-string-append (separator strings)
  (apply #'concatenate 
	 'string 
	 (car strings) 
	 (mapcan #'(lambda (x) (list separator x)) (cdr strings))))

;;;List access

(defmacro tea::char (str)
  `(char ,str 0))

(defmacro-synonym tea::nthchar char)

(defmacro-synonym tea::nthchdr subseq)

(defmacro tea::nth (l n) `(nth ,n ,l))
;;(setf-value-from-function 'tea::nth)

(defun nth-setter (l n val)
  (setf (nth n l) val))
(%defsetf tea::nth nth-setter)

(defmacro tea::nthcdr (l n) `(nthcdr ,n ,l))
;;(setf-value-from-function 'tea::nthcdr)

(defmacro-synonym tea::reverse! nreverse)
(defmacro-synonym tea::append! nconc)
(defmacro-synonym tea::append append)
(defmacro-synonym tea::reverse reverse)
(defmacro-synonym tea::reduce reduce)

;;This is a hack.See below

(defmacro tea::walk (fn &rest ls)
  (let ((the-ls (mapcar #'(lambda (x) `(the list ,x)) ls)))
    `(progn (map nil (closure ,fn) ,@the-ls) ,(car the-ls))))

;;The compiler refuses to compile this:

;(defmacro tea::walk (fn &rest ls)
;  `(mapc (closure ,fn) ,@ls))


(defmacro tea::map (fn &rest ls)
  `(mapcar (closure ,fn) ,@ls))

(defmacro ->boolean (arg)
  `(if ,arg t ,arg))

(defmacro tea::any (fn &rest ls)
  `(some (closure ,fn) ,@ls))

(defmacro tea::any? (fn &rest args)
  `(->boolean (some (closure ,fn) ,@args)))

(defmacro tea::every (fn &rest ls)
   `(every (closure ,fn) ,@ls))

(defmacro tea::every? (fn &rest args)
  `(->boolean (every (closure ,fn) ,@args)))

(defmacro tea::map! (fn l)
  `(maplist (function (lambda (x) (setf (car x) (funcall (closure ,fn) (car x)))))
	   ,l))

(defmacro tea::everycdr? (fn &rest lists)
  `(block it-aint-necessarilly-so
     (mapl (function (lambda (&rest args) 
		       (or (apply (closure ,fn) args)
			   (return-from it-aint-necessarilly-so nil))))
	   ,@lists)
     t))

(defmacro tea::anycdr? (fn &rest lists)
  `(block il-y-en-a
     (mapl (function (lambda (&rest args) 
		       (if (apply (closure ,fn) args)
			   (return-from il-y-en-a t))))
	   ,@lists)
     nil))


(defmacro tea::string-posq (obj l)
  `(position ,obj (the string ,l)))

(defmacro tea::posq (obj l)
  `(position ,obj (the list ,l)))

(defmacro tea::pos (pred obj l)
  `(position ,obj (the list ,l) :test ,pred))

(defmacro tea::lastcdr (l)
  `(last ,l))

(defmacro tea::last (l)
  `(car (last ,l)))

(defmacro-synonym tea::cons* list*)
(defmacro-synonym tea::list* list*)

(defmacro tea::memq (obj ls)
  `(member ,obj ,ls))

(defmacro tea::memq? (obj ls)
  `(member ,obj ,ls))

(defmacro tea::mem? (pred object list)
  `(member ,object ,list :test ,pred))

(defmacro tea::mem (pred object list)
  `(member ,object ,list :test ,pred))

(defmacro tea::delq (object list)
  `(remove ,object ,list))

(defmacro tea::del (pred object list)
  `(remove ,object ,list :test ,pred))

(defmacro tea::delq! (object list)
  `(delete ,object ,list))

(defmacro tea::del! (pred object list)
  `(delete ,object ,list :test ,pred))

(defmacro tea::assq (object list)
  `(assoc ,object ,list))

(defmacro tea::assq? (object list)
  `(assoc ,object ,list))

(defmacro tea::ass (pred object list)
  `(assoc ,object ,list :test ,pred))

(defmacro tea::list->string (l)
  `(map 'string (function (lambda (x) x)) ,l))

(defmacro tea::string->list (l)
  `(map 'list (function (lambda (x) x)) ,l))

(defmacro tea::map-string (fn l)
  `(map 'string (closure ,fn) ,l))

(defmacro tea::map-string! (fn l)
  `(map-into ,l (closure ,fn) ,l))

;;Vectors:

(defmacro tea::make-vector (n)
  `(make-array (list ,n)))

;;The following forms added by JT Tue Jul 15 17:21:06 EDT 1997
;;Fills in an obvious gap.

(defmacro tea::vref (vect n)
  `(svref ,vect ,n))

(defmacro tea::vset (vect n obj)
  `(setf (svref ,vect ,n) ,obj))

(defun vsetter (vect n obj)
  (setf (svref vect n) obj))

(%defsetf tea::vref vsetter)

(defmacro tea::list->vector (l)
  `(map 'vector (function (lambda (x) x)) ,l))

(defmacro tea::vector->list (v)
  `(map 'list (function (lambda (x) x)) ,v))

;;Chars
(defmacro tea::char->string (char)
  `(map 'string (function (lambda (x) x)) (list ,char)))

(defmacro-synonym tea::vector-length length)

;;Chars
(defmacro-synonym tea::char->ascii char-code)
(defmacro-synonym tea::ascii->char code-char)

(defmacro-synonym tea::char-upcase char-upcase)
(defmacro-synonym tea::char-downcase char-downcase)

(defmacro-synonym tea::sort sort)
(defmacro tea::sort-list (l pred)
  `(sort (copy-list ,l) ,pred))

(defmacro-synonym tea::sort-list! sort)

(defun hash-order (x y)
  (< (sxhash x) (sxhash y)))

(defmacro-synonym tea::hash-< hash-order)
  
(defun sort-list-hashfully (l)
  (sort (copy-list l) #'hash-order))
;;(setf-value-from-function 'tea::sort-list-hashfully)

(defmacro-synonym tea::string-hash sxhash)
(defmacro-synonym tea::symbol-hash sxhash)
(defmacro-synonym tea::descriptor-hash sxhash)

;;The foolowing definition was modified and moved to hash.lisp
;;(defmacro-synonym tea::object-hash sxhash)

;;General

(defmacro-synonym tea::eval eval)

(defmacro-synonym tea::retrieve-y-or-n-from-user yes-or-no-p)

;; Modification by W. M. Farmer Mon Mar 22 2004
;; The following line was added:

#+clisp (defun bye () (user::quit))
#+cmu (defun bye () (common-lisp::quit))
#+allegro (defun bye () (user::exit))

(defmacro-synonym tea::quit bye)
(defmacro-synonym tea::exit bye)
;;Variables

(defvar tea::*maximum-number-of-arguments* call-arguments-limit)
(defvar tea::else 't)
;(defvar tea::nil '())
(defvar tea::t 't)
(defvar tea::nil lisp::nil)

(defvar tea::value-true 't)
(defvar tea::value-false lisp::nil)
;;Booleans:

(proclaim '(inline tea::true))
(defun tea::true (&rest args)
  (declare (ignore args))
  't)
(setf-value-from-function 'tea::true)
(proclaim '(inline tea::false))
(defun tea::false (&rest args)
  (declare (ignore args))
  '())
(setf-value-from-function 'tea::false)

(defmacro-synonym tea::false? null)

(proclaim '(inline tea::true?))
(defun tea::true? (x) (not (null x)))
(setf-value-from-function 'tea::true?)

(defun tea::boolean? (arg)
  (or (eq arg (tea::true)) (eq arg (tea::false))))

(setf-value-from-function 'tea::boolean?)

;;No fixnums as far as I can tell, so fake it:

(defmacro-synonym tea::fx+ +)
(defmacro-synonym tea::fx- -)
(defmacro-synonym tea::fx* *)
(defmacro-synonym tea::fx= =)
(defmacro-synonym tea::fx< <)
(defmacro-synonym tea::fx<= <=)
(defmacro-synonym tea::fx> >)
(defmacro-synonym tea::fx>= >=)
(defmacro-synonym tea::fixnum-logand logand)
(defmacro-synonym tea::fixnum-logior logior)
(defmacro-synonym tea::fixnum-lognot lognot)


(defmacro tea::fixnum? (i)
  `(typep ,i 'fixnum))

(defmacro tea::ratio? (r)
  `(typep ,r 'ratio))

(defmacro-synonym tea::ashl ash)
(defmacro-synonym tea::fixnum-ashl ash)
(defmacro-synonym tea::->float float)
(defmacro-synonym tea::float? floatp)
(defvar fx1 1)

(defun tea::intern-symbol (sym)
  (intern (symbol-name sym)))

;;;Some macros which are not part of TEA.

(defmacro tea::remove-duplicates (predicate une-liste &optional from-end)
  `(remove-duplicates (the list ,une-liste) :test ,predicate :from-end ,from-end))

)
