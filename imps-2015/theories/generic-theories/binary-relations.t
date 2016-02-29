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

(herald BINARY-RELATIONS)

(include-files
   (files (imps theories/generic-theories/binary-relations-and-predicates)))

;;; Basic properties

;;; Transitive closure

(def-recursive-constant BR%PARTIAL%TRANS%CLOSURE
  "lambda(f:[nn,sets[ind_1,ind_1],sets[ind_1,ind_1]],
     lambda(n:nn,r:sets[ind_1,ind_1],
       if(n=0, 
          r, 
          lambda(s:sets[ind_1,ind_1],
            lambda(x,y:ind_1, 
              if(forsome(z:ind_1, #(s(x,z)) and #(r(z,y))),
                 an%individual, 
                 ?unit%sort)))
            (f(n-1,r)))))"
  (theory generic-theory-1)
  (definition-name br%partial%trans%closure))

(def-theorem BR%PARTIAL%TRANS%CLOSURE-TOTAL-AUX
  "forall(r:sets[ind_1,ind_1],n:zz,
     0<=n implies #(br%partial%trans%closure(n,r)))"
  (theory generic-theory-1)
  (proof
   (
    (induction integer-inductor ("n"))
    )))

(def-theorem BR%PARTIAL%TRANS%CLOSURE-IS-TOTAL
  "total_q{br%partial%trans%closure,[nn,sets[ind_1,ind_1],sets[ind_1,ind_1]]}"
  (theory generic-theory-1)
  (usages d-r-convergence)
  (proof
   (
    insistent-direct-inference
    (apply-macete-with-minor-premises br%partial%trans%closure-total-aux)
    (apply-macete-with-minor-premises nn-in-quasi-sort_h-o-real-arithmetic)
    )))

(def-theorem BR%PARTIAL%TRANS%CLOSURE-LEMMA-1
  "forall(m:nn,n:zz,r:sets[ind_1,ind_1],
     0<=n
      implies
     forall(x,y,z:ind_1,
      #(br%partial%trans%closure(m,r)(x,y))
       and
      #(br%partial%trans%closure(n,r)(y,z))
       implies
      #(br%partial%trans%closure(m+n+1,r)(x,z))))"
  (theory generic-theory-1)
  (proof
   (
    (induction trivial-integer-inductor ("n"))
    beta-reduce-repeatedly
    (unfold-single-defined-constant (1 2) br%partial%trans%closure)
    simplify
    (unfold-single-defined-constant (0) br%partial%trans%closure)
    simplify
    (instantiate-existential ("z_$0"))
    (backchain "with(p:prop,forall(x,z:ind_1,p))")
    (instantiate-existential ("y"))
    )))

(def-theorem BR%PARTIAL%TRANS%CLOSURE-LEMMA-2
  "forall(n:zz,r:sets[ind_1,ind_1],
     br%symmetric(r)
      and
     0<=n
      implies
     forall(x,y:ind_1,
      #(br%partial%trans%closure(n,r)(x,y))
       implies
      #(br%partial%trans%closure(n,r)(y,x))))"
  (theory generic-theory-1)
  (proof
   (
    (unfold-single-defined-constant (0) br%symmetric)
    (induction trivial-integer-inductor ("n"))
    beta-reduce-repeatedly
    (unfold-single-defined-constant-globally br%partial%trans%closure)
    (instantiate-existential ("z_$0"))
    (move-to-ancestor 8)
    (unfold-single-defined-constant (0) br%partial%trans%closure)
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(r:sets[ind_1,ind_1],forall(x,y:ind_1,#(r(x,y)) implies #(r(y,x))))"
     ("z_$0" "y"))
    (instantiate-universal-antecedent 
     "with(p:prop,forall(x,y:ind_1,p))" ("x" "z_$0"))
    (cut-with-single-formula "#(br%partial%trans%closure(0,r)(y,z_$0))")
    (force-substitution "1+t" "0+t+1" (0))
    (apply-macete-with-minor-premises br%partial%trans%closure-lemma-1)
    auto-instantiate-existential
    simplify
    (unfold-single-defined-constant (0) br%partial%trans%closure)
    )))

(def-constant BR%TRANS%CLOSURE
  "lambda(r:sets[ind_1,ind_1],
     lambda(x,y:ind_1, 
       if(forsome(n:nn, #(br%partial%trans%closure(n,r)(x,y))),
          an%individual, 
          ?unit%sort)))"
  (theory generic-theory-1))

(def-theorem TRANSITIVE-CLOSURE-IS-TRANSITIVE
  "forall(r:sets[ind_1,ind_1], 
     br%transitive(br%trans%closure(r)))"
  (theory generic-theory-1)
  (proof
   (
    unfold-defined-constants
    (raise-conditional (0))
    (raise-conditional (0))
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,not(p))")
    (instantiate-existential ("n_$0+n+1"))
    (apply-macete-with-minor-premises br%partial%trans%closure-lemma-1)
    auto-instantiate-existential
    (apply-macete-with-minor-premises nn-in-quasi-sort_h-o-real-arithmetic)
    )))

(def-theorem TRANS-CLOSURE-OF-REFLEXIVE-RELATION-IS-REFLEXIVE
  "forall(r:sets[ind_1,ind_1], 
     br%reflexive(r) implies br%reflexive(br%trans%closure(r)))"
  (theory generic-theory-1)
  (proof
   (
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    simplify
    (instantiate-existential ("0"))
    (unfold-single-defined-constant (0) br%partial%trans%closure)
    )))

(def-theorem TRANS-CLOSURE-OF-SYMMETRIC-RELATION-IS-SYMMETRIC
  "forall(r:sets[ind_1,ind_1], 
     br%symmetric(r) implies br%symmetric(br%trans%closure(r)))"
  (theory generic-theory-1)
  (proof
   (
    unfold-defined-constants
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("n"))
    (apply-macete-with-minor-premises br%partial%trans%closure-lemma-2)
    direct-inference
    (unfold-single-defined-constant (0) br%symmetric)
    (apply-macete-with-minor-premises nn-in-quasi-sort_h-o-real-arithmetic)
    )))


;;; Unions

(def-constant BR%UNION
  "lambda(r,s:sets[ind_1,ind_1],
     lambda(x,y:ind_1, if(#(r(x,y)) or #(s(x,y)), an%individual, ?unit%sort)))"
  (theory generic-theory-1))

(def-theorem UNION-OF-REFLEXIVE-RELATIONS-IS-REFLEXIVE
  "forall(r,s:sets[ind_1,ind_1],
     br%reflexive(r) and br%reflexive(s) implies br%reflexive(br%union(r,s)))"
  (theory generic-theory-1)
  (proof
   (
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (case-split-on-conditionals (0))
    )))

(def-theorem UNION-OF-SYMMETRIC-RELATIONS-IS-SYMMETRIC
  "forall(r,s:sets[ind_1,ind_1],
     br%symmetric(r) and br%symmetric(s) implies br%symmetric(br%union(r,s)))"
  (theory generic-theory-1)
  (proof
   (
    unfold-defined-constants
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (case-split-on-conditionals (0))
    (case-split-on-conditionals (0))
    )))

(def-theorem TRANS-CLOSURE-OF-UNION-OF-EQUIV-RELS-IS-AN-EQUIV-REL
  "forall(r,s:sets[ind_1,ind_1],
     br%equiv%relation(r) and br%equiv%relation(s)
      implies
     br%equiv%relation(br%trans%closure(br%union(r,s))))"
  (theory generic-theory-1)
  (proof
   (
    (unfold-single-defined-constant-globally br%equiv%relation)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises 
     trans-closure-of-reflexive-relation-is-reflexive)
    (apply-macete-with-minor-premises 
     union-of-reflexive-relations-is-reflexive)
    direct-inference
    (apply-macete-with-minor-premises 
     trans-closure-of-symmetric-relation-is-symmetric)
    (apply-macete-with-minor-premises 
     union-of-symmetric-relations-is-symmetric)
    direct-inference
    (apply-macete-with-minor-premises transitive-closure-is-transitive)
    )))

