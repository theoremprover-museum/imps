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


(herald normal-subgroups)


(include-files
  (files (imps theories/groups/cosets)))



;;; Definitions

(def-constant NORMAL
  "lambda(a:sets[gg], 
     forall(g,h:gg, h in a implies (g mul h mul inv(g)) in a))"
  (theory groups))

(def-constant RIGHT%COSET%APP
  "lambda(f:[gg,gg],a:sets[gg], 
     lambda(b:sets[gg], 
       iota(c:sets[gg], 
         forsome(g:gg, b = right%trans(a,g) and 
                       c = right%trans(a,f(g))))))"
  (theory groups))

(def-constant RIGHT%COSETS
  "lambda(a:sets[gg],
     indic{b:sets[gg], forsome(g:gg, b=right%trans(a,g))})"
  (theory groups))


;;; Preliminary lemmas

(def-theorem RIGHT%COSET%APP-IS-TOTAL
  "total_q{right%coset%app,[[gg,gg],sets[gg],[sets[gg],sets[gg]]]}"
  (theory groups)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally right%coset%app)
    simplify-insistently
    )))

(def-theorem RIGHT%COSETS-IS-TOTAL
  "total_q{right%cosets,[sets[gg],sets[sets[gg]]]}"
  (theory groups)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally right%cosets)
    simplify-insistently
    )))


;;; Lemmas

(def-theorem RIGHT%COSETS-MEMBERSHIP
  "forall(a,b:sets[gg],
     a in right%cosets(b) iff forsome(g:gg, a = right%trans(b,g)))"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally right%cosets)
    simplify-insistently
    )))

(def-theorem NORMAL-IFF-COSETS-PROPERTY
  "forall(a:sets[gg],
     normal(a) iff forall(g:gg, left%trans(g,a) = right%trans(a,g)))"
  (theory groups)
  (usages transportable-macete)
  (proof				; 61 nodes
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0 0 0)")
     extensionality
     direct-inference
     simplify-insistently
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment 
       "node added by `direct-and-antecedent-inference-strategy' at (0 0 0)")
      (instantiate-existential ("(g mul i) mul inv(g)"))
      (block 
       (script-comment "node added by `instantiate-existential' at (0 0)")
       (backchain "with(g,x_0:gg,x_0=g);")
       (backchain "with(p:prop,forall(g,h:gg,p));"))
      simplify)
     (block 
      (script-comment 
       "node added by `direct-and-antecedent-inference-strategy' at (1 0 0)")
      (contrapose "with(p:prop,not(p));")
      (instantiate-existential ("(inv(g) mul i) mul inv(inv(g))"))
      (backchain "with(p:prop,forall(g,h:gg,p));")
      simplify))
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0 1 0 0)")
     (instantiate-universal-antecedent "with(p:prop,forall(g:gg,p));" ("g"))
     (incorporate-antecedent "with(f:sets[gg],f=f);")
     (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
     direct-and-antecedent-inference-strategy
     (instantiate-universal-antecedent 
      "with(g:gg,a:sets[gg],
         indic{h:gg,  forsome(i:gg,i in a and h=g mul i)}
          subseteq 
         indic{h:gg,  forsome(i:gg, i in a and h=i mul g)});"
      ("g mul h"))
     (block 
      (script-comment 
       "node added by `instantiate-universal-antecedent' at (0 0 0)")
      (contrapose "with(p:prop,not(p));")
      simplify-insistently
      auto-instantiate-existential)
     (block 
      (script-comment 
       "node added by `instantiate-universal-antecedent' at (0 0 1)")
      (contrapose "with(h,g:gg,f:[gg,prop],(g mul h) in pred_to_indic(f));")
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (contrapose "with(p:prop,not(p));")
      (force-substitution "g mul h" "i_$0 mul g" (0))
      (weaken (0))
      simplify))

    )))

(def-theorem NORMAL-IFF-CONJUGATES-PROPERTY
  "forall(a:sets[gg],
     normal(a) iff forall(g:gg, set%conjugate(a,g) = a))"
  (theory groups)
  (usages transportable-macete)
  (proof				; 18 nodes
   (
    (unfold-single-defined-constant-globally set%conjugate)
    (force-substitution 
     "right%trans(left%trans(inv(g),a),g)=a" 
     "left%trans(inv(g),a) = right%trans(a,inv(g))"
     (0))
    (apply-macete-with-minor-premises normal-iff-cosets-property)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop, forall(g:gg,p))")
    (force-substitution "g" "inv(inv(g))" (0 1))
    (backchain "with(p:prop, forall(g:gg,p))")
    simplify
    (force-substitution 
     "right%trans(left%trans(inv(g),a),g)=a" 
     "right%trans(right%trans(left%trans(inv(g),a),g),inv(g)) = 
      right%trans(a,inv(g))"
     (0))
    simplify
    (apply-macete-with-minor-premises rev%right-translation-macete)
    )))

(def-theorem NORMAL-IMPLIES-COSETS-PROPERTY
  "forall(a:sets[gg],g:gg, 
     normal(a) implies left%trans(g,a) = right%trans(a,g))"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem normal-iff-cosets-property ("a"))
    (backchain "with(p:prop, forall(g:gg,p))")
    )))

(def-compound-macete SIMPLIFY-NORMAL-SUBGROUP-EXPRESSIONS
  (repeat
   (without-minor-premises normal-implies-cosets-property)
   (without-minor-premises idempotence-of-subgroups)
   set%mul-right%trans-associativity
   right%trans-set%mul-associativity))


;;; Lemmas for factor group theorem

(def-theorem RIGHT-COSET-INVERSION
  "forall(a:sets[gg],g:gg,
     normal(a)
       implies
     right%coset%app(inv,a)(right%trans(a,g)) = right%trans(a,inv(g)))"
  (theory groups)
  (usages transportable-macete)
  (proof				; 36 nodes
   (
    (unfold-single-defined-constant-globally right%coset%app)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("g"))
    (force-substitution "b_$0" "right%trans(a,inv(g_$0))" (0))
    (weaken (2))
    (instantiate-theorem normal-iff-cosets-property ("a"))
    (apply-macete-with-minor-premises right-translation-macete)
    (instantiate-existential ("g"))
    simplify
    (backchain-backwards "with(p:prop, forall(g:gg,p))")
    (apply-macete-with-minor-premises right%trans-left%trans-associativity)
    (backchain 
     "with(g_$0,g:gg,a:sets[gg], right%trans(a,g)=right%trans(a,g_$0));")
    (backchain-backwards "with(p:prop, forall(g:gg,p))")
    simplify
    )))

(def-theorem RIGHT-COSET-MULTIPLICATION
  "forall(a:sets[gg],
     subgroup(a) and normal(a) 
       implies
     forall(g,h:gg, 
       right%trans(a,g) set%mul right%trans(a,h) 
        = 
       right%trans(a, g mul h)))"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises simplify-normal-subgroup-expressions)
    (apply-macete-with-minor-premises simplify-set-translations)
    )))

(def-compound-macete SIMPLIFY-RIGHT-COSET-EXPRESSIONS
  (series
   (repeat
    (without-minor-premises right-coset-inversion)
    (without-minor-premises right-coset-multiplication))
   simplify))

(def-theorem RIGHT-COSET-LEFT-IDENTITY
  "forall(a,b:sets[gg],
     subgroup(a) and normal(a) and b in right%cosets(a)
       implies
     a set%mul b = b)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises right%cosets-membership)
    direct-and-antecedent-inference-strategy
    (force-substitution "b" "right%trans(a,g)" (0 1))
    (force-substitution "a" "right%trans(a,e)" (0))
    (apply-macete-with-minor-premises simplify-right-coset-expressions)
    simplify
    )))

(def-theorem RIGHT-COSET-RIGHT-IDENTITY
  "forall(a,b:sets[gg],
     subgroup(a) and normal(a) and b in right%cosets(a)
       implies
     b set%mul a = b)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises right%cosets-membership)
    direct-and-antecedent-inference-strategy
    (force-substitution "b" "right%trans(a,g)" (0 1))
    (force-substitution "a" "right%trans(a,e)" (1))
    (apply-macete-with-minor-premises simplify-right-coset-expressions)
    simplify
    )))

(def-theorem RIGHT-COSET-LEFT-INVERSE
  "forall(a,b:sets[gg],
     subgroup(a) and normal(a) and b in right%cosets(a)
       implies
     right%coset%app(inv,a)(b) set%mul b = a)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises right%cosets-membership)
    direct-and-antecedent-inference-strategy
    (force-substitution "b" "right%trans(a,g)" (0 1))
    (force-substitution "a" "right%trans(a,e)" (0))
    (weaken (0))
    simplify
    (apply-macete-with-minor-premises simplify-right-coset-expressions)
    simplify
    )))

(def-theorem RIGHT-COSET-RIGHT-INVERSE
  "forall(a,b:sets[gg],
     subgroup(a) and normal(a) and b in right%cosets(a)
       implies
     b set%mul right%coset%app(inv,a)(b) = a)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises right%cosets-membership)
    direct-and-antecedent-inference-strategy
    (force-substitution "b" "right%trans(a,g)" (0 1))
    (force-substitution "a" "right%trans(a,e)" (1))
    (weaken (0))
    simplify
    (apply-macete-with-minor-premises simplify-right-coset-expressions)
    simplify
    )))


;;; Factor group theorem

(def-theorem FACTOR-GROUPS-ARE-GROUPS
  "forall(a:sets[gg], 
     subgroup(a) and normal(a)
       implies 
     group{right%cosets(a), set%mul, a, right%coset%app(inv,a)})"
  (theory groups)
  (usages transportable-macete)
  (proof				; 44 nodes
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    (apply-macete-with-minor-premises right%cosets-membership)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("g_$0 mul g"))
    (force-substitution 
     "x set%mul y" "right%trans(a,g_$0) set%mul right%trans(a,g)" (0))
    (apply-macete-with-minor-premises right-coset-multiplication)
    (apply-macete-with-minor-premises right%cosets-membership)
    (instantiate-existential ("e"))
    simplify
    (apply-macete-with-minor-premises right%cosets-membership)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("inv(g)"))
    (force-substitution "x" "right%trans(a,g)" (0))
    (apply-macete-with-minor-premises right-coset-inversion)
    (antecedent-inference "with(p:prop, forsome(g:gg,p))")
    (apply-macete-with-minor-premises right-coset-left-identity)
    (apply-macete-with-minor-premises right-coset-right-identity)
    (apply-macete-with-minor-premises right-coset-left-inverse)
    (apply-macete-with-minor-premises right-coset-right-inverse)
    (apply-macete-with-minor-premises set%mul-associativity)
    direct-and-antecedent-inference-strategy
    )))

