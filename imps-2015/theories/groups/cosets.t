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


(herald cosets)

(include-files
  (files (imps theories/groups/group-actions)))


;;; Parsing and printing

(def-parse-syntax set%mul
  (left-method infix-operator-method) 
  (binding 100))

(def-print-syntax set%mul
  (token " set%mul ")
  (method present-non-associative-infix-operator) 
  (binding 100))


;;; Definitions

(def-constant LEFT%TRANS
  "lambda(g:gg,a:sets[gg],
     indic{h:gg, forsome(i:gg, (i in a) and h=g mul i)})"
  (theory groups))

(def-constant RIGHT%TRANS
  "lambda(a:sets[gg],g:gg, 
       indic{h:gg, forsome(i:gg, (i in a) and h=i mul g)})"
  (theory groups))

(def-constant SET%MUL
  "lambda(a,b:sets[gg], 
     indic{g:gg, forsome(h,i:gg, (h in a) and (i in b) and g=h mul i)})"
  (theory groups))

(def-constant SET%CONJUGATE
  "lambda(a:sets[gg],g:gg, right%trans(left%trans(inv(g),a),g))"
  (theory groups))


;;; Preliminary lemmas

(def-theorem LEFT%TRANS-IS-TOTAL
  "total_q{left%trans,[gg,sets[gg],sets[gg]]}"
  (theory groups)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally left%trans)
    simplify-insistently
    )))

(def-theorem RIGHT%TRANS-IS-TOTAL
  "total_q{right%trans,[sets[gg],gg,sets[gg]]}"
  (theory groups)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally right%trans)
    simplify-insistently
    )))

(def-theorem SET%MUL-IS-TOTAL
  "total_q{set%mul,[sets[gg],sets[gg],sets[gg]]}"
  (theory groups)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally set%mul)
    simplify-insistently
    )))

(def-theorem SET%CONJUGATE-IS-TOTAL
  "total_q{set%conjugate,[sets[gg],gg,sets[gg]]}"
  (theory groups)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally set%conjugate)
    simplify-insistently
    )))


;;; Theory interpretations

(def-theorem LEFT%TRANS->RIGHT%TRANS-OBLIGATION
  "lambda(g:gg,a:sets[gg],right%trans(a,g))=
     lambda(g:gg,a:sets[gg],lambda(x:gg,
       if(forsome(i_$0:gg, i_$0 in a and x=i_$0 mul g), 
          an%individual, 
          ?unit%sort)))"
  lemma
  (theory groups)
  (proof
   (
    (unfold-single-defined-constant-globally right%trans)
    extensionality
    simplify
    )))

(def-theorem RIGHT%TRANS->LEFT%TRANS-OBLIGATION
  "lambda(a:sets[gg],g:gg,left%trans(g,a))=
     lambda(a:sets[gg],g:gg,lambda(x:gg,
       if(forsome(i_$0:gg, i_$0 in a and x=g mul i_$0), 
          an%individual, 
          ?unit%sort)))"
  lemma
  (theory groups)
  (proof
   (
    (unfold-single-defined-constant-globally left%trans)
    extensionality
    simplify
    )))

(def-theorem SUBGROUP->SUBGROUP-OBLIGATION
  "subgroup = 
   lambda(a:sets[gg],
     nonempty_indic_q{a}
      and 
     forall(g,h:gg,g in a and h in a implies (h mul g) in a)
      and 
     forall(g:gg,g in a implies inv(g) in a))"
  lemma
  (theory groups)
  (proof
   (
    (unfold-single-defined-constant-globally subgroup)
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(p:prop, forall(g,h:gg, p))" ("h" "g"))
    (instantiate-universal-antecedent 
     "with(p:prop, forall(g:gg, p))" ("g"))
    (instantiate-universal-antecedent 
     "with(p:prop, forall(g,h:gg, p))" ("h" "g"))
    )))

(def-translation LEFT%TRANS<->RIGHT%TRANS
  (source groups)
  (target groups)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs
   (mul "lambda(x,y:gg, y mul x)")
   (left%trans "lambda(g:gg,a:sets[gg], right%trans(a,g))")
   (right%trans "lambda(a:sets[gg],g:gg, left%trans(g,a))")
   (subgroup subgroup))
  force-under-quick-load
  (theory-interpretation-check using-simplification))

(def-theorem TRIVIAL-LEFT-TRANSLATION
  "forall(a:sets[gg], left%trans(e,a)=a)"
  (theory groups)
  (usages rewrite transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally left%trans)
    direct-inference
    extensionality
    direct-inference
    simplify
    (case-split-on-conditionals (0))
    )))

(def-theorem LEFT%TRANS-ASSOCIATIVITY
  "forall(g,h:gg,a:sets[gg], 
     left%trans(h mul g,a) = left%trans(h,(left%trans(g,a))))"
  (theory groups)
  (usages transportable-macete)
  (proof				; 28 nodes
   (

    (unfold-single-defined-constant-globally left%trans)
    direct-inference
    extensionality
    direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0 0 0)")
     (instantiate-existential ("g mul i_$0"))
     (instantiate-existential ("i_$0")))
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' 
       at (1 0 0 0 0)")
     (contrapose "with(p:prop,not(p));")
     (instantiate-existential ("i"))
     simplify)

    )))

(def-theorem TRIVIAL-RIGHT-TRANSLATION
  ;; "forall(a:sets[gg], right%trans(a,e)=a)"
  trivial-left-translation
  (theory groups)
  (usages rewrite transportable-macete)
  (translation left%trans<->right%trans)
  (proof existing-theorem))

(def-theorem RIGHT%TRANS-ASSOCIATIVITY
  ;; "forall(g,h:gg,a:sets[gg], 
  ;;    right%trans(a,g mul h)=right%trans(right%trans(a,g),h))"
  left%trans-associativity
  (theory groups)
  (usages transportable-macete)
  (translation left%trans<->right%trans)
  (proof existing-theorem))

(def-translation ACT->LEFT%TRANS
  (source group-actions)
  (target groups)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (uu "sets[gg]"))
  (constant-pairs
   (mul "lambda(x,y:gg, y mul x)")
   (act "lambda(a:sets[gg],g:gg, left%trans(g,a))"))
  (theory-interpretation-check using-simplification))

(def-translation ACT->RIGHT%TRANS
  (source group-actions)
  (target groups)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (uu "sets[gg]"))
  (constant-pairs
   (act "right%trans"))
  (theory-interpretation-check using-simplification))

(def-theorem LEFT%TRANS-RIGHT%TRANS-ASSOCIATIVITY
  "forall(a:sets[gg], g,h:gg, 
     left%trans(g,right%trans(a,h)) = right%trans(left%trans(g,a),h))"
  (theory groups)
  (usages transportable-macete)
  (proof				; 43 nodes
   (

    unfold-defined-constants
    direct-inference
    extensionality
    direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' 
       at (0 0 0 0 0)")
     (instantiate-existential ("g mul i_$0 mul inv(h)"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 0)")
      (instantiate-existential ("i_$1"))
      (force-substitution "i_$0" "i_$1 mul h" (0))
      (weaken (0 1 2))
      simplify)
     (block 
      (script-comment "node added by `instantiate-existential' at (0 1)")
      (weaken (0 1 2))
      simplify))
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' 
       at (1 0 0 0 0)")
     (contrapose "with(p:prop,not(p));")
     (instantiate-existential ("inv(g) mul i_$0 mul h"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 0)")
      (instantiate-existential ("i"))
      (force-substitution "i_$0" "g mul i" (0))
      (weaken (0 1 2))
      simplify)
     (block 
      (script-comment "node added by `instantiate-existential' at (0 1)")
      (weaken (0 2 3))
      simplify))

    )))

(def-theorem RIGHT%TRANS-LEFT%TRANS-ASSOCIATIVITY
  left%trans-right%trans-associativity
  ;; "forall(a:sets[gg], g,h:gg, 
  ;;    right%trans(left%trans(h,a),g) = left%trans(h,right%trans(a,g)))"
  (theory groups)
  (usages transportable-macete)
  (translation left%trans<->right%trans)
  (proof existing-theorem))

(def-theorem TRIVIAL-CONJUGATION
  "forall(a:sets[gg], set%conjugate(a,e)=a)"
  (theory groups)
  (usages rewrite transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally set%conjugate)
    simplify
    )))

(def-theorem SET%CONJUGATE-ASSOCIATIVITY
  "forall(a:sets[gg],g,h:gg, 
     set%conjugate(a,g mul h)=set%conjugate(set%conjugate(a,g),h))"
  (theory groups)
  (usages transportable-macete)
  (proof				; Macete menu takes some time here
   (
    (unfold-single-defined-constant-globally set%conjugate)
    simplify
    (apply-macete-with-minor-premises left%trans-associativity)
    (apply-macete-with-minor-premises right%trans-associativity)
    (apply-macete-with-minor-premises left%trans-right%trans-associativity)
    direct-inference
    )))

(def-translation ACT->SET%CONJUGATE
  (source group-actions)
  (target groups)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (uu "sets[gg]"))
  (constant-pairs
   (act "set%conjugate"))
  (theory-interpretation-check using-simplification))


;;; Lemmas transported from group-actions

(def-theorem LEFT-LEFT%TRANS-INV
  ;; "forall(alpha:sets[gg],g:gg, 
  ;;    left%trans(inv(g),left%trans(g,alpha))=alpha)"
  right-act-inv
  (theory groups)
  (usages rewrite transportable-macete)
  (translation act->left%trans)
  (proof existing-theorem))

(def-theorem RIGHT-LEFT%TRANS-INV
  ;; "forall(alpha:sets[gg],g:gg, 
  ;;    left%trans(g,left%trans(inv(g),alpha))=alpha)"
  left-act-inv
  (theory groups)
  (usages rewrite transportable-macete)
  (translation act->left%trans)
  (proof existing-theorem))

(def-theorem LEFT-RIGHT%TRANS-INV
  ;; "forall(alpha:sets[gg],g:gg, 
  ;;    right%trans(right%trans(alpha,inv(g)),g)=alpha)"
  left-act-inv
  (theory groups)
  (usages rewrite transportable-macete)
  (translation act->right%trans)
  (proof existing-theorem))

(def-theorem RIGHT-RIGHT%TRANS-INV
  ;; "forall(alpha:sets[gg],g:gg, 
  ;;    right%trans(right%trans(alpha,g),inv(g))=alpha)"
  right-act-inv
  (theory groups)
  (usages rewrite transportable-macete)
  (translation act->right%trans)
  (proof existing-theorem))

(def-theorem REVERSE-LEFT%TRANS-ASSOCIATIVITY
  ;; "forall(alpha:sets[gg],g,h:gg, 
  ;;    left%trans(h,left%trans(g,alpha))=left%trans(h mul g,alpha))"
  reverse-act-associativity
  (theory groups)
  (usages transportable-macete)
  (translation act->left%trans)
  (proof existing-theorem))

(def-theorem REVERSE-RIGHT%TRANS-ASSOCIATIVITY
  ;; "forall(alpha:sets[gg],g,h:gg, 
  ;;    right%trans(right%trans(alpha,g),h)=right%trans(alpha,g mul h))"
  reverse-act-associativity
  (theory groups)
  (usages transportable-macete)
  (translation act->right%trans)
  (proof existing-theorem))

(def-theorem REVERSE-SET%CONJUGATE-ASSOCIATIVITY
  ;; "forall(alpha:sets[gg],g,h:gg, 
  ;;    set%conjugate(set%conjugate(alpha,g),h)=
  ;;    set%conjugate(alpha,g mul h))"
  reverse-act-associativity
  (theory groups)
  (usages transportable-macete)
  (translation act->set%conjugate)
  (proof existing-theorem))

(def-compound-macete SIMPLIFY-SET-TRANSLATIONS
  (series
   (repeat 
    reverse-left%trans-associativity
    reverse-right%trans-associativity
    reverse-set%conjugate-associativity)
   simplify))

(def-theorem LEFT-TRANSLATION-MACETE
  ;; "forall(alpha,beta:sets[gg],g:gg, 
  ;;    alpha=beta iff left%trans(g,alpha)=left%trans(g,beta))"
  action-macete
  reverse
  (theory groups)
  (usages transportable-macete)
  (translation act->left%trans)
  (proof existing-theorem))

(def-theorem RIGHT-TRANSLATION-MACETE
  ;; "forall(alpha,beta:sets[gg],g:gg, 
  ;;    alpha=beta iff right%trans(alpha,g)=right%trans(beta,g))"
  action-macete
  reverse
  (theory groups)
  (usages transportable-macete)
  (translation act->right%trans)
  (proof existing-theorem))


;;; Left%trans and right%trans lemmas

(def-theorem SUBGROUP-IS-LEFT%TRANS-STABILIZER
  "forall(a:sets[gg],g:gg, subgroup(a) implies left%trans(g,a) = a iff g in a)"
  (theory groups)
  (usages transportable-macete)
  (proof				; 32 nodes
   (

    (unfold-single-defined-constant-globally left%trans)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0 0 0)")
     (contrapose "with(a,f:sets[gg],f=a);")
     extensionality
     (instantiate-existential ("g"))
     simplify-insistently
     (instantiate-existential ("e"))
     (apply-macete-with-minor-premises subgroup-membership)
     simplify)
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0 0 1)")
     extensionality
     direct-inference
     simplify-insistently
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment 
       "node added by `direct-and-antecedent-inference-strategy' at (0 0 0)")
      (cut-with-single-formula "x_0 in a")
      simplify
      (block 
       (script-comment "node added by `cut-with-single-formula' at (1)")
       (force-substitution "x_0" "g mul i" (0))
       (apply-macete-with-minor-premises subgroup-membership)))
     (block 
      (script-comment 
       "node added by `direct-and-antecedent-inference-strategy' at (1)")
      (contrapose "with(p:prop,not(p));")
      (instantiate-existential ("inv(g) mul x_0"))
      (apply-macete-with-minor-premises subgroup-membership)
      simplify))

    )))

(def-theorem SUBGROUP-IS-RIGHT%TRANS-STABILIZER
  subgroup-is-left%trans-stabilizer
  ;; "forall(a:sets[gg],g:gg, 
  ;;    subgroup(a) implies right%trans(a,g)=a iff g in a)"
  (theory groups)
  (translation left%trans<->right%trans)
  (proof existing-theorem))


;;; Set%mul lemmas

(def-theorem SET%MUL-ASSOCIATIVITY
  "forall(a,b,c:sets[gg],g:gg, 
     (a set%mul b) set%mul c = a set%mul (b set%mul c))"
  (theory groups)
  (usages transportable-macete)
  (proof				; 52 nodes
   (

    (unfold-single-defined-constant-globally set%mul)
    direct-inference
    extensionality
    simplify-insistently
    direct-inference
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' 
       at (0 0 0 0 0)")
     (instantiate-existential ("i mul i_$0" "h"))
     (instantiate-existential ("i_$0" "i"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 2)")
      (force-substitution "x_0" "h_$0 mul i_$0" (0))
      (force-substitution "h_$0" "h mul i" (0))
      (weaken (0 1 2 3 4 5))
      simplify))
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' 
       at (1 0 0 0 0)")
     (contrapose "with(p:prop,not(p));")
     (instantiate-existential ("i_$1" "h_$0 mul h_$1"))
     (instantiate-existential ("h_$1" "h_$0"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 2)")
      (force-substitution "x_0" "h_$0 mul i_$0" (0))
      (force-substitution "i_$0" "h_$1 mul i_$1" (0))
      (weaken (0 1 2 3 4 5))
      simplify))

    )))

(def-theorem IDEMPOTENCE-OF-SUBGROUPS
  "forall(a:sets[gg], subgroup(a) implies a set%mul a = a)"
  (theory groups)
  (usages transportable-macete)
  (proof				; 25 nodes
   (

    (unfold-single-defined-constant-globally set%mul)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "e in a")
    (block 
     (script-comment "node added by `cut-with-single-formula' at (0)")
     extensionality
     direct-inference
     simplify-insistently
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment 
       "node added by `direct-and-antecedent-inference-strategy' at (0 0 0)")
      (cut-with-single-formula "x_0 in a")
      simplify
      (block 
       (script-comment "node added by `cut-with-single-formula' at (1)")
       (force-substitution "x_0" "h_$0 mul i_$0" (0))
       (apply-macete-with-minor-premises subgroup-membership)))
     (block 
      (script-comment 
       "node added by `direct-and-antecedent-inference-strategy' at (1)")
      (contrapose "with(p:prop,not(p));")
      (instantiate-existential ("e" "x_0"))
      simplify))
    (apply-macete-with-minor-premises subgroup-membership)

    )))

(def-theorem SET%MUL-RIGHT%TRANS-ASSOCIATIVITY
  "forall(a,b:sets[gg],g:gg, 
     a set%mul right%trans(b,g) = right%trans(a set%mul b, g))"
  (theory groups)
  (usages transportable-macete)
  (proof				; 44 nodes
   (

    unfold-defined-constants
    direct-inference
    extensionality
    direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' 
       at (0 0 0 0 0)")
     (instantiate-existential ("h_$0 mul i"))
     (instantiate-existential ("i" "h_$0"))
     simplify)
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' 
       at (1 0 0 0 0)")
     (contrapose "with(p:prop,not(p));")
     (instantiate-existential ("i mul g" "h"))
     (instantiate-existential ("i"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 2)")
      (force-substitution "x_0" "i_$0 mul g" (0))
      (force-substitution "i_$0" "h mul i" (0))
      (weaken (0 1 2 3 4))
      simplify))

    )))

(def-theorem RIGHT%TRANS-SET%MUL-ASSOCIATIVITY
  "forall(a,b:sets[gg],g:gg, 
     right%trans(a,g) set%mul b = a set%mul left%trans(g,b))"
  (theory groups)
  (usages transportable-macete)
  (proof				; 47 nodes
   (

    unfold-defined-constants
    direct-inference
    extensionality
    direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' 
       at (0 0 0 0 0)")
     (instantiate-existential ("g mul i_$0" "i"))
     (instantiate-existential ("i_$0"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 2)")
      (force-substitution "x_0" "h_$0 mul i_$0" (0))
      (force-substitution "h_$0" "i mul g" (0))
      (weaken (0 1 2 3 4))
      simplify))
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' 
       at (1 0 0 0 0)")
     (contrapose "with(p:prop,not(p));")
     (instantiate-existential ("i" "h_$0 mul g"))
     (instantiate-existential ("h_$0"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 2)")
      (force-substitution "x_0" "h_$0 mul i_$0" (0))
      simplify))

    )))


;;; Right coset lemmas

(def-theorem OVERLAPPING-RIGHT-COSETS
  "forall(a:sets[gg],g,h:gg, 
     subgroup(a)
      implies
     (right%trans(a,g) = right%trans(a,h)
       or
      right%trans(a,g) disj right%trans(a,h)))"
  (theory groups)
  (usages transportable-macete)
  (proof				; 49 nodes
   (

    (unfold-single-defined-constant-globally right%trans)
    insistent-direct-inference-strategy
    (contrapose "with(p:prop,not(p));")
    extensionality
    direct-inference
    (incorporate-antecedent 
     "with(x,h:gg,a:sets[gg], 
        x in indic{h_$0:gg, 
          forsome(i_$0:gg, i_$0 in a and h_$0=i_$0 mul h)});")
    (incorporate-antecedent "with(x:gg,f:sets[gg],x in f);")
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' 
       at (0 0 0 0 0 0 0 0 0)")
     (instantiate-existential ("i mul g mul inv(h)"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 0)")
      (apply-macete-with-minor-premises mul-associativity)
      (apply-macete-with-minor-premises subgroups-closed-under-mul)
      simplify
      (force-substitution "h" "inv(i_$0) mul x" (0))
      (block 
       (script-comment "node added by `force-substitution' at (0)")
       (force-substitution "g" "inv(i_$1) mul x" (0))
       (block 
	(script-comment "node added by `force-substitution' at (0)")
	(weaken (0 5))
	simplify
	(apply-macete-with-minor-premises subgroup-membership))
       (block 
	(script-comment "node added by `force-substitution' at (1)")
	(force-substitution "x" "i_$1 mul g" (0))
	(weaken (0))
	simplify))
      (block 
       (script-comment "node added by `force-substitution' at (1)")
       (force-substitution "x" "i_$0 mul h" (0))
       (weaken (5))
       simplify))
     simplify)
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' 
       at (0 0 1 0 0 0 0 0 0)")
     (contrapose "with(p:prop,not(p));")
     (instantiate-existential ("i_$0 mul h mul inv(g)"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 0)")
      (apply-macete-with-minor-premises mul-associativity)
      (apply-macete-with-minor-premises subgroups-closed-under-mul)
      simplify
      (force-substitution "h" "inv(i_$1) mul x" (0))
      (block 
       (script-comment "node added by `force-substitution' at (0)")
       (force-substitution "g" "inv(i) mul x" (0))
       (block 
	(script-comment "node added by `force-substitution' at (0)")
	simplify
	(apply-macete-with-minor-premises subgroup-membership))
       (block 
	(script-comment "node added by `force-substitution' at (1)")
	(force-substitution "x" "i mul g" (0))
	(weaken (5))
	simplify))
      (block 
       (script-comment "node added by `force-substitution' at (1)")
       (force-substitution "x" "i_$1 mul h" (0))
       (weaken (1))
       simplify))
     simplify)

    )))


