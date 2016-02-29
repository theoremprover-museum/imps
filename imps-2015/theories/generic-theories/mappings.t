;% Copyright (c) 1990-1994 The MITRE Corporation
;% 
;% Authors: W. M. Farmer, J. D. Guttman, F. J. Thayer
;%   
;% The MITRE Corporation (MITRE) provides this software to you without
;% charge to use, copy, modify or enhance for any legitimate purpose
;% provided you reproduce MITRE's copyright notice in any copy or
;% derivative work of this software.
;% 
;% This software is the copyright work of MITRE.  No ownership or other
;% proprietary interest in this software is granted you other than what
;% is granted in this license.
;% 
;% Any modification or enhancement of this software must identify the
;% part of this software that was modified, by whom and when, and must
;% inherit this license including its warranty disclaimers.
;% 
;% MITRE IS PROVIDING THE PRODUCT "AS IS" AND MAKES NO WARRANTY, EXPRESS
;% OR IMPLIED, AS TO THE ACCURACY, CAPABILITY, EFFICIENCY OR FUNCTIONING
;% OF THIS SOFTWARE AND DOCUMENTATION.  IN NO EVENT WILL MITRE BE LIABLE
;% FOR ANY GENERAL, CONSEQUENTIAL, INDIRECT, INCIDENTAL, EXEMPLARY OR
;% SPECIAL DAMAGES, EVEN IF MITRE HAS BEEN ADVISED OF THE POSSIBILITY OF
;% SUCH DAMAGES.
;% 
;% You, at your expense, hereby indemnify and hold harmless MITRE, its
;% Board of Trustees, officers, agents and employees, from any and all
;% liability or damages to third parties, including attorneys' fees,
;% court costs, and other related costs and expenses, arising out of your
;% use of this software irrespective of the cause of said liability.
;% 
;% The export from the United States or the subsequent reexport of this
;% software is subject to compliance with United States export control
;% and munitions control restrictions.  You agree that in the event you
;% seek to export this software or any derivative work thereof, you
;% assume full responsibility for obtaining all necessary export licenses
;% and approvals and for assuring compliance with applicable reexport
;% restrictions.
;% 
;% 
;% COPYRIGHT NOTICE INSERTED: Mon Apr 11 11:42:27 EDT 1994


(herald MAPPINGS)

(include-files 
  (files (imps theories/generic-theories/indicators)
	 (imps theories/generic-theories/pure-generic-theories)))


;;; Parse specifications

(def-parse-syntax m-composition
  (token oo)
  (left-method infix-operator-method)
  (binding 201))

(def-parse-syntax m-domain
  (token dom)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-range
  (token ran)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-image
  (token image)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-inverse-image
  (token inv_image)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-inverse
  (token inverse)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-id
  (token id)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-restrict
  (token restrict)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-restrict2
  (token restrict2)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-surjective?
  (token surjective_q)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-injective?
  (token injective_q)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-bijective?
  (token bijective_q)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-surjective-on?
  (token surjective_on_q)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-injective-on?
  (token injective_on_q)
  (null-method prefix-operator-method)
  (binding 160))

(def-parse-syntax m-bijective-on?
  (token bijective_on_q)
  (null-method prefix-operator-method)
  (binding 160))


;;; Print specifications

(def-print-syntax m-composition
  (token " oo ")
  (method present-binary-infix-operator)
  (binding 201))

(def-print-syntax m-domain
  (token dom)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-range
  (token ran)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-image
  (token image)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-inverse-image
  (token inv_image)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-inverse
  (token inverse)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-id
  (token id)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-restrict
  (token restrict)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-restrict2
  (token restrict2)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-surjective?
  (token surjective_q)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-injective?
  (token injective_q)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-bijective?
  (token bijective_q)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-surjective-on?
  (token surjective_on_q)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-injective-on?
  (token injective_on_q)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax m-bijective-on?
  (token bijective_on_q)
  (method present-prefix-operator)
  (binding 160))


;;; TeX print specifications

(def-print-syntax m-composition
  tex
  (token " \\circ ")
  (method present-tex-binary-infix-operator)
  (binding 201))

(def-print-syntax m-domain
  tex
  (token " \\mbox{dom} ")
  (method present-tex-prefix-operator)
  (binding 160))

(def-print-syntax m-range
  tex
  (token " \\mbox{ran} ")
  (method present-tex-prefix-operator)
  (binding 160))

(def-print-syntax m-image
  tex
  (token image)
  (method present-tex-direct-image-operator)
  (binding 160))

(def-print-syntax m-inverse-image
  tex
  (token inv_image)
  (method present-tex-inverse-image-operator)
  (binding 160))

(def-print-syntax m-inverse
  tex
  (token inv)
  (method present-tex-inverse-operator)
  (binding 160))

(def-print-syntax m-id
  tex
  (token id)
  (method present-tex-id-operator)
  (binding 160))

(def-print-syntax m-restrict
  tex
  (token "\\; \\grave{}\\!\\!{|}\\; ")
  (method present-tex-binary-infix-operator)
  (binding 160))

(def-print-syntax m-surjective?
  tex
  (token surjective)
  (method present-tex-prefix-operator)
  (binding 160))

(def-print-syntax m-injective?
  tex
  (token injective)
  (method present-tex-prefix-operator)
  (binding 160))

(def-print-syntax m-bijective?
  tex
  (token bijective)
  (method present-tex-prefix-operator)
  (binding 160))

(def-print-syntax m-surjective-on?
  tex
  (token surjective%on)
  (method present-tex-prefix-operator)
  (binding 160))

(def-print-syntax m-injective-on?
  tex
  (token injective%on)
  (method present-tex-prefix-operator)
  (binding 160))

(def-print-syntax m-bijective-on?
  tex
  (token bijective%on)
  (method present-tex-prefix-operator)
  (binding 160))


;;; Quasi-constructors

(def-quasi-constructor M-COMPOSITION
  "lambda(f:[ind_2,ind_3],g:[ind_1,ind_2], lambda(x:ind_1, f(g(x))))"
  (language pure-generic-theory-3)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-DOMAIN
  "lambda(f:[ind_1,ind_2], indic(x:ind_1, #(f(x))))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-RANGE
  "lambda(f:[ind_1,ind_2], indic(y:ind_2, forsome(x:ind_1, y=f(x))))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-IMAGE
  "lambda(f:[ind_1,ind_2],a:sets[ind_1],
     indic(y:ind_2, forsome(x:ind_1, (x in a) and y=f(x))))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-INVERSE-IMAGE
  "lambda(f:[ind_1,ind_2],b:sets[ind_2], b oo f)"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-INVERSE
  "lambda(f:[ind_1,ind_2], 
     lambda(x:ind_2, iota(y:ind_1, f(y)=x)))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-ID
  "lambda(a:sets[ind_1],
     lambda(x:ind_1, if(x in a, x, ?ind_1)))"
  (language pure-generic-theory-1)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-RESTRICT
  "lambda(f:[ind_1,ind_2],a:sets[ind_1],
     lambda(x:ind_1, if(x in a, f(x), ?ind_2)))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-RESTRICT2
  "lambda(f:[ind_1,ind_2,ind_3],a:sets[ind_1],b:sets[ind_2],
     lambda(x:ind_1,y:ind_2, if(x in a and y in b, f(x,y), ?ind_3)))"
  (language pure-generic-theory-3)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-SURJECTIVE?
  "lambda(f:[ind_1,ind_2], 
     forall(x:ind_1, x in dom(f)) and forall(y:ind_2, y in ran(f)))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-INJECTIVE?
  "lambda(f:[ind_1,ind_2], 
     forall(x_1,x_2:ind_1, f(x_1)=f(x_2) implies x_1=x_2))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-BIJECTIVE?
  "lambda(f:[ind_1,ind_2], surjective_q(f) and injective_q(f))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-SURJECTIVE-ON?
  "lambda(f:[ind_1,ind_2],a:sets[ind_1],b:sets[ind_2], 
     dom(f)=a and ran(f)=b)"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-INJECTIVE-ON?
  "lambda(f:[ind_1,ind_2],a:sets[ind_1],
     forall(x_1,x_2:ind_1, 
       ((x_1 in a) and (x_2 in a) and f(x_1)=f(x_2)) implies x_1=x_2))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor M-BIJECTIVE-ON?
  "lambda(f:[ind_1,ind_2],a:sets[ind_1],b:sets[ind_2],
     surjective_on_q(f,a,b) and injective_on_q(f,a))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))



;;;(make-operator *parse* 'oo 'm-composition '() infix-operator-method 201)
;;;(make-operator *parse* 'dom 'm-domain prefix-operator-method `() 160)
;;;(make-operator *parse* 'ran 'm-range prefix-operator-method `() 160)
;;;(make-operator *parse* 'image 'm-image prefix-operator-method `() 160)
;;;(make-operator *parse* 'inv_image 'm-inverse-image prefix-operator-method `() 160)
;;;(make-operator *parse* 'inverse 'm-inverse prefix-operator-method `() 160)
;;;(make-operator *parse* 'id 'm-id prefix-operator-method `() 160)
;;;(make-operator *parse* 'surjective_q 'm-surjective? prefix-operator-method `() 160)
;;;(make-operator *parse* 'injective_q 'm-injective? prefix-operator-method `() 160)
;;;(make-operator *parse* 'bijective_q 'm-bijective? prefix-operator-method `() 160)
;;;(make-operator *parse* 'surjective_on_q 'm-surjective-on? prefix-operator-method `() 160)
;;;(make-operator *parse* 'injective_on_q 'm-injective-on? prefix-operator-method `() 160)
;;;(make-operator *parse* 'bijective_on_q 'm-bijective-on? prefix-operator-method `() 160)
;;;(make-operator *parse* 'restrict 'm-restrict prefix-operator-method `() 160)
;;;
;;;(make-presentation-format *form* 'm-composition " oo " present-binary-infix-operator 201)
;;;(make-presentation-format *form* 'm-domain 'dom present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-range 'ran present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-image 'image present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-inverse-image 'inv_image present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-inverse 'inverse present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-id 'id present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-surjective? 'surjective_q present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-injective? 'injective_q present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-bijective? 'bijective_q present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-surjective-on? 'surjective_on_q present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-injective-on? 'injective_on_q present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-bijective-on? 'bijective_on_q present-prefix-operator 160)
;;;(make-presentation-format *form* 'm-restrict 'restrict present-prefix-operator 160)
;;;
;;;
;;;(define (PRESENT-TEX-DIRECT-IMAGE-OPERATOR formatter op args bp)
;;;  (ignore bp op)
;;;  `(,(present-tree formatter (car args) 0) \( ,(present-tree formatter (cadr args) 0) \)))
;;;
;;;(define (PRESENT-TEX-INVERSE-IMAGE-OPERATOR formatter op args bp)
;;;  (ignore bp op)
;;;  `(,(present-tree formatter (car args) 0) " ^{-1} " \( ,(present-tree formatter (cadr args) 0) \)))
;;;
;;;(define (PRESENT-TEX-INVERSE-OPERATOR formatter op args bp)
;;;  (ignore bp op)
;;;  `(,(present-tree formatter (car args) 0) " ^{-1} "))
;;;
;;;(define (PRESENT-TEX-id-OPERATOR formatter op args bp)
;;;  (ignore bp op)
;;;  `(" id_{" ,(present-tree formatter (car args) 0) "}  ")) 
;;;
;;;(make-presentation-format *tex-form* 'm-composition " \\circ " present-tex-binary-infix-operator 201)
;;;(make-presentation-format *tex-form* 'm-domain " \\mbox{dom } " present-tex-prefix-operator 160)
;;;(make-presentation-format *tex-form* 'm-range " \\mbox{ran } " present-tex-prefix-operator 160)
;;;(make-presentation-format *tex-form* 'm-image 'image present-tex-direct-image-operator 160)
;;;(make-presentation-format *tex-form* 'm-inverse-image 'inv_image present-tex-inverse-image-operator 160)
;;;(make-presentation-format *tex-form* 'm-inverse 'inv present-tex-inverse-operator 160)
;;;(make-presentation-format *tex-form* 'm-id 'id present-tex-id-operator 160)
;;;(make-presentation-format *tex-form* 'm-surjective? 'surjective present-tex-prefix-operator 160)
;;;(make-presentation-format *tex-form* 'm-injective? 'injective present-tex-prefix-operator 160)
;;;(make-presentation-format *tex-form* 'm-bijective? 'bijective present-tex-prefix-operator 160)
;;;(make-presentation-format *tex-form* 'm-surjective-on? 'surjective%on present-tex-prefix-operator 160)
;;;(make-presentation-format *tex-form* 'm-injective-on? 'injective%on present-tex-prefix-operator 160)
;;;(make-presentation-format *tex-form* 'm-bijective-on? 'bijective%on present-tex-prefix-operator 160)
;;;(make-presentation-format *tex-form* 'm-restrict "\\; \\grave{}\\!\\!{|}\\; " present-binary-infix-operator 201)
;;;
