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


(herald (assorted bird))



;; This file begins the Imps-cementation of Richard Bird's "Introduction to the
;; Theory of Lists" (PRG-56)
;; 


(push-current-theory)
(push-current-syntax)
(set (use-string-form?) '#t)

(def-language bird-language
  (base-types elem value))

(def-theory bird
  (language bird-language)
  (component-theories h-o-real-arithmetic))

(define bird (name->theory 'bird))
(define pure-generic-theory-4 (name->theory 'pure-generic-theory-4))
(theory-import-transportable-rewrite-rules bird (list pure-generic-theory-4 sequences))

(def-translation seq->bird
  (source sequences)
  (target bird)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 elem))
  (theory-interpretation-check using-simplification))

(set (current-theory) bird)

(theory-import-transportable-rewrite-rules
 bird
 (list pure-generic-theory-4 sequences))

(define bird-ensemble (build-theory-ensemble bird))
(define bird-2
  (theory-ensemble-find-theory-multiple bird-ensemble 2))
(define bird-3
  (theory-ensemble-find-theory-multiple bird-ensemble 3))
(theory-ensemble-export-transportable-rwrs bird-ensemble)

(set (current-theory) bird-2)

(def-constant map
  "lambda(f:[elem_0,elem_1], lambda(s:[nn,elem_0], lambda(m:nn, f(s(m)))))"
  ;;
  ;;defined in curried form
  ;;
  (theory bird-2-tuples))
  
(def-theorem map-means-compose
  "forall(f:[elem_0,elem_1], s:[nn,elem_0], map(f)(s)=f oo s)"
  (theory bird-2-tuples)
  (usages transportable-macete)
  ;;
  ;; proved trivially
  ;; 
  )

(def-theorem domain-of-total-map
  "forall(f:[elem_0,elem_1], s:[nn,elem_0], total_q{f,[elem_0,elem_1]} implies
dom{map(f)(s)}=dom{s})"
  (theory bird-2-tuples)
  (usages transportable-macete)
  ;;
  ;; proved trivially
  ;; 
  )

(def-theorem map-f-is-total
  "forall(y:[nn,elem_0],f:[elem_0,elem_1], #(map(f)(y)))"
  (theory bird-2-tuples)
  (usages rewrite transportable-rewrite)
  ;;
  ;;  eliminate definitions and simplify.  
  ;; 
  )
  


(def-theorem domain-of-almost-total-map
  "forall(f:[elem_0,elem_1], s:[nn,elem_0], 
        forall(x:elem_0, x in ran{s} implies #(f(x)))
       implies
	dom{map(f)(s)}=dom{s})"
  (theory bird-2-tuples)
  (usages transportable-macete)
  (proof "$THEORIES/bird/proofs/domain-of-almost-total-map.t"))

(def-theorem map-through-nil
  "forall(f:[elem_0,elem_1], map(f)(nil{elem_0})=nil{elem_1})"
  (theory bird-2-tuples)
  (usages transportable-macete transportable-rewrite rewrite)
  ;; Unfold definitions and insistently simplify
  )

(def-theorem map-totality
  "total_q{map,[[elem_0,elem_1],[[nn,elem_0],[nn,elem_1]]]}"
  (theory bird-2-tuples)
  (usages d-r-convergence)
  ;; Unfold definitions and insistently simplify
  )
 
(def-theorem map-cons
  "forall(f:[elem_0,elem_1], s:[nn,elem_0], a:elem_0,
      map(f)(cons{a,s})=cons{f(a),map(f)(s)})"
  (theory bird-2-tuples)
  (usages rewrite transportable-rewrite)
 (proof "$THEORIES/bird/proofs/map-cons.t"))

(def-inductor elem-sequence-inductor
  sequence-induction
  (theory bird)
  (translation seq->bird)
  (base-case-hook simplify))

(def-inductor elem_0-sequence-inductor
  sequence-induction-for-elem-sequence-inductor
  (theory bird-0)
  (translation bird-to-bird-0)
  (base-case-hook simplify))

(def-theorem map-append
  "forall(f:[elem_0,elem_1],x,y:[nn,elem_0], 
      f_seq_q{x} and total_q{f,[elem_0,elem_1]}
     implies
      map(f)(append{x,y})=append{map(f)(x), map(f)(y)})"
  (theory bird-2-tuples)
  (usages transportable-macete)
  (proof  "$THEORIES/bird/proofs/map-append.t"))


(def-theory-ensemble-instances
 bird
 (multiples 2)
 (target-multiple 3))
;;; Replaces
;;; 
;;; (transport-defined-sorts-and-constants-to-theory-multiple bird-ensemble '(2) 3)
;;;

(theory-ensemble-install-overloadings-for-defined-constants bird-ensemble 3)

(def-theorem map-distributes-over-composition
 "forall(f:[elem_0,elem_1], g:[elem_1,elem_2], map(g oo f) = (map(g)) oo (map(f)))"
 (theory bird-3-tuples)
 (usages transportable-macete)
 (proof "$THEORIES/bird/proofs/map-comp-distributes.t"))

(def-theorem map-inverse
 "forall(f:[elem_0,elem_1], injective_q{f} and surjective_q{f}
 implies inverse{map(inverse{f})} = map(f) )"
 (theory bird-3-tuples)
 (usages transportable-macete)
 (proof "$THEORIES/bird/proofs/map-inverse.t"))

(def-theorem map-inverse-1
  "forall(f:[elem_0,elem_1],  injective_q{f} and surjective_q{f}
 implies inverse{map(f)} = map(inverse{f}))"
  (theory bird-3-tuples)
  (usages transportable-macete)
  (proof "$THEORIES/bird/proofs/map-inverse-1.t"))





;; (set (current-theory) bird)


;(theory-build-recursive-definition
; birdbase
; 'filter1
; (qr "lambda(fil:[[elem,prop],[nn,elem],[nn,elem]],
;	lambda(pred:[elem,prop], s:[nn,elem], if(s=nil{elem}, nil{elem},lambda(y:[nn,elem],
;		if(pred(s(0)), cons{s(0),y},y))(fil(pred,drop{s,1})))))")
; 'filter1)



; (theory-build-recursive-definition
;  birdbase
;  'filter2
;  (qr "lambda(fil:[[elem,prop],[nn,elem],[nn,elem]],
; 	lambda(pred:[elem,prop], s:[nn,elem],
; 	 if(s=nil{elem} or not(f_seq_q{s}) or not(f_seq_q{fil(pred,drop{s,1})}),
; 	    nil{elem},
;           if(pred(s(0)),cons{s(0),fil(pred,drop{s,1})},fil(pred,drop{s,1})))))")
;  'filter2)



;; (qr "forall(pred:[elem,prop],filter1(pred,nil{elem})=nil{elem})")

;(theory-verify-and-add-theorem
; birdbase
; (qr "forall(pred:[elem,prop],s:[nn,elem],
;  f_seq_q{s} implies
;  filter1(pred,s)=if(
;  s=nil{elem}, nil{elem},
;  pred(s(0)), cons{s(0),filter1(pred,drop{s,1})},
;  filter1(pred,drop{s,1})))")
; 'filter1-beta-for-fseqs
; '()
; "")
;
;(theory-verify-and-add-theorem
; birdbase
; (qr "forall(pred:[elem,prop],s:[nn,elem],
;  f_seq_q{s} implies #(filter1(pred,s)))")
; 'filter1-defined-for-fseqs
; '()
; "")

(pop-current-syntax)
(pop-current-theory)
