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


(herald GROUP-ACTIONS)

(include-files
  (files (imps theories/groups/groups)
	 (imps theories/groups/subgroups)))


;;; Group action theory

(def-language GROUP-ACTION-LANGUAGE
  (embedded-language groups-language)
  (base-types uu)
  (constants
   (act "[uu,gg,uu]")))

(def-theory GROUP-ACTIONS
  (language group-action-language)
  (component-theories groups)
  (axioms
   (act-id
    "forall(alpha:uu, act(alpha,e) = alpha)"
    rewrite transportable-macete)
   (act-associativity
    "forall(alpha:uu,g,h:gg, act(alpha,g mul h) = act(act(alpha,g),h))" 
    transportable-macete)))


;;; Definitions

(def-constant ORBIT
  "lambda(alpha:uu, indic{beta:uu, forsome(g:gg, beta = act(alpha,g))})"
  (theory group-actions))

(def-constant STABILIZER
  "lambda(alpha:uu, indic{g:gg, act(alpha,g)=alpha})"
  (theory group-actions))


;;; Preliminary lemmas

(def-theorem ACT-IS-TOTAL
  "total_q(act,[uu,gg,uu])"
  (theory group-actions)
  (usages d-r-convergence transportable-macete)
  (proof
   (
    insistent-direct-inference
    (instantiate-theorem act-associativity ("x_0" "x_1" "e"))
    )))

(def-theorem ORBIT-IS-TOTAL
  "total_q(orbit,[uu,sets[uu]])"
  (theory group-actions)
  (usages d-r-convergence transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally orbit)
    simplify-insistently
    )))

(def-theorem STABILIZER-IS-TOTAL
  "total_q(stabilizer,[uu,sets[gg]])"
  (theory group-actions)
  (usages d-r-convergence transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally stabilizer)
    simplify-insistently
    )))

(def-theorem REVERSE-ACT-ASSOCIATIVITY
  "forall(alpha:uu,g,h:gg, act(act(alpha,g),h) = act(alpha,g mul h))"
  (theory group-actions)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises act-associativity)
    simplify
    )))

(def-theorem ACTION-BY-STABILIZER-MEMBER
  "forall(alpha:uu,g:gg, g in stabilizer(alpha) implies act(alpha,g)=alpha)"
  (theory group-actions)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally stabilizer)
    simplify
    )))


;;; Simplification

(def-theorem LEFT-ACT-INV
  "forall(alpha:uu,g:gg, act(act(alpha,inv(g)),g) = alpha)"
  (theory group-actions)
  (usages rewrite transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises reverse-act-associativity)
    simplify
    )))

(def-theorem RIGHT-ACT-INV
  "forall(alpha:uu,g:gg, act(act(alpha,g),inv(g)) = alpha)"
  (theory group-actions)
  (usages rewrite transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises reverse-act-associativity)
    simplify
    )))

(def-compound-macete SIMPLIFY-ACTIONS
  (series
   (repeat reverse-act-associativity)
   simplify))


;;; Act to mul theory interpretations

(def-translation ACT->LEFT-MUL
  (source group-actions)
  (target groups)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (uu "gg"))
  (constant-pairs
   (mul "lambda(x,y:gg, y mul x)")
   (act "lambda(x,y:gg, y mul x)"))
  force-under-quick-load
  (theory-interpretation-check using-simplification))

(def-translation ACT->RIGHT-MUL
  (source group-actions)
  (target groups)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (uu "gg"))
  (constant-pairs
   (act "mul"))
  force-under-quick-load
  (theory-interpretation-check using-simplification))

(def-translation ACT->CONJUGATE
  (source group-actions)
  (target groups)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (uu "gg"))
  (constant-pairs
   (act "lambda(g,h:gg, (inv(h) mul g) mul h)"))
  force-under-quick-load
  (theory-interpretation-check using-simplification))


;;; Lemmas

(def-theorem ACTION-MACETE
  "forall(alpha,beta:uu,g:gg, alpha=beta iff act(alpha,g) = act(beta,g))"
  reverse
  (theory group-actions)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem act-associativity ("alpha" "g" "inv(g)"))
    (contrapose "with(g,h:gg,alpha,beta:uu, act(alpha,g)=act(beta,h))")
    (force-substitution "act(alpha,g)" "act(beta,g)" (0))
    simplify
    )))

(def-theorem STABILIZERS-ARE-SUBGROUPS
  "forall(alpha:uu, subgroup(stabilizer(alpha)))"
  (theory group-actions)
  (usages transportable-macete)
  (proof
   (
    unfold-defined-constants
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("e"))
    simplify
    (apply-macete-with-minor-premises act-associativity)
    simplify
    (apply-macete-with-minor-premises action-macete)
    (instantiate-existential ("g_$0"))
    simplify
    )))


