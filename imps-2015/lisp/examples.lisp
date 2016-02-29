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

(in-package "TEA")

(block
    
    (define-syntax (test-expr expr right-value)
      `(format '#t "Evaluating ~S.~%  Evaluates to: ~S~%  Should evaluate to ~S.~%" ',expr ,expr ,right-value))
  
  (test-expr (lset  *haha* 3) 3)
  (test-expr (define-operation ((ha) *haha*) ((setter val) (lambda (v) (set *haha* v))))
	     'ha)
  (test-expr (ha) 3)
  (test-expr (set (ha) 99) 99)
  (test-expr (ha) 99)
  
  (test-expr (define-settable-operation (carro x)) 'carro)
  (test-expr (define-settable-operation (cdrro x)) 'cdrro)
  (test-expr (define-predicate listap) 'listap)
  (test-expr (define (haz-lista a b)
	       (object '#f
		       ((listap soi) 't)
		       ((carro soi) a)
		       ((cdrro soi) b)
		       (((setter carro) soi z) (set a z))
		       (((setter cdrro) soi z) (set b z)))) 'some-value)
  (test-expr (set fuba (haz-lista 2 3)) "{object NIL}")
  (test-expr (carro fuba) 2)
  (test-expr (cdrro fuba) 3)
  (test-expr (set (carro fuba) 9) 9)
  (test-expr (carro fuba) 9)
  (test-expr (set luba (haz-lista 99 'b))  "{object NIL}")
  (test-expr (set ruba (join luba fuba)) "{object NIL}")
  (test-expr (carro ruba) 99)
  (test-expr  (define (haz-lista a b)
	       (object (lambda (z) (list a z))
		       ((listap soi) 't)
		       ((carro soi) a)
		       ((cdrro soi) b)
		       (((setter carro) soi z) (set a z))
		       (((setter cdrro) soi z) (set b z)))) 'some-value)
  (test-expr (define ra (haz-lista 2 3)) 'some-value)
  (test-expr (ra 'i) '(2 i))  
  (test-expr (set (carro ra) 'my-house) 'my-house)
  (test-expr (ra 'j) '(my-house j))
  (test-expr (funcall ra 'j) '(my-house j))
  (test-expr (apply ra '(u)) '(my-house u))
  (test-expr (define-structure-type 
	       employee 
	       name 
	       age 
	       (((carro soi) (employee-name soi))))
	     "{object NIL}")
  (test-expr (set (employee-name (stype-master employee-stype)) 'javier) 'javier)
  (test-expr employee-name 'some-value)
  (test-expr (set ha (make-employee)) "{object NIL}")
  (test-expr (employee-name ha) 'javier)
  (test-expr (carro ha) 'javier)
  (test-expr (define (gurra x)
	       (iterate loop ((x x) (y 1))
			(cond ((= x 1) y)
			      (else (loop (- x 1) (* x y))))))
	     'some-list)
  (test-expr (gurra 10) 3628800)
  (test-expr (funcall gurra 10) 3628800)
  (test-expr (apply gurra (list 10)) 3628800)
  (test-expr (map ra '(a b c)) '((my-house a)(my-house b)(my-house c)))

  (test-expr (select employee-name 
		     ((ra) '()) 
		     ((employee-name gurra) 3) 
		     (else 987))
	     3)
  
  (test-expr (select 'bongo ((ra) '()) ((employee-name gurra) 3) (else 987))
	     987)
  (test-expr (define fafa (make-hash-table equiv? 'ha)) "{Hash Table HA}")
  (test-expr (set (table-entry fafa '(t o n t o)) 3) 'some-value)
  (test-expr (table-entry fafa '(t o n t o)) 3)
  (test-expr (table-entry fafa '(t i a)) '())

  (test-expr (set la (make-set-table 'ha)) 'some-value)
  (test-expr (table-entry la '(a b)) nil)
  (test-expr (set (table-entry la '(a b)) 3) 3)
  (test-expr (table-entry la '(a b)) 3)
  
  (test-expr (set faro '(a g e)) '(a g e))
  (test-expr (set (car faro) 3) 3)
  (test-expr faro '(3 g e))

  (test-expr (set ga (let ((a 3)) 
		       (flet (((fuba soi x) (set a (+ x a))) 
			      ((muba soi x) (set a (- a x)))) 
			 (list #'muba #'fuba)))) 
	     'some-value)
  (test-expr (funcall (car ga) 'l 3) 0)
  (test-expr (set sa (make-object)) "{object NIL}")
  (test-expr (define-operation tarro) "{operation TARRO}")
  (test-expr (define-operation barro) "{operation BARRO}")
  (test-expr (refurnish-object sa nil (tarro (car ga)) (barro (cadr ga))) "{object NIL}")
  (test-expr (tarro sa 60) "-60")
  (test-expr (set (symbol-pathname 'imps) (make-pathname "/home/vc/jt/sys/lisp/" nil "lisp")) 'some-value)
  (test-expr (set fuba (open (->filename '(imps basic)) '(in))) 'some-value)
  (test-expr (read fuba) "(in-package \"TEA-IMPLEMENTATION\")")
  (test-expr (close fuba) 'some-value)
  (test-expr (with-open-ports ((haha (open (->filename '(imps lal)) '(out))))
			      (write haha (+ 2 3))) 'some-value)
  (test-expr (define (implode char-list)
	       (let ((port (string->input-port (list->string char-list))))
		 (set (port-read-table port) *vanilla-read-table*)
		 (read port))) 'some-expr)
  (test-expr (implode (string->list "this is a list too implode")) 'THIS)
  (test-expr (with-output-to-string 
	      p 
	      (let ((q (join  ra p (object nil)))) 
		(format q "~A" "HAHAH")
		(display "Fous-moi la paix" q)))
	     "HAHAHFous-moi la paix"))

;;(setf *package* (find-package "TEA"))
