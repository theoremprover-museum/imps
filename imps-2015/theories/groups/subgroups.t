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


(herald subgroups)


(include-files
  (files (imps theories/groups/groups)))


;;; Definitions

(def-constant SUBGROUP
  "lambda(a:sets[gg], 
     nonempty_indic_q{a} and
     forall(g,h:gg, ((g in a) and (h in a)) implies ((g mul h) in a)) and
     forall(g:gg, (g in a) implies (inv(g) in a)))"
  (theory groups))

(def-constant GG%SUBGROUP 
  "sort_to_indic(gg)" 
  (theory groups))

(def-constant E%SUBGROUP 
  "singleton{e}"
  (theory groups))


;;; Trivial subgroups

(def-theorem GG-IS-A-SUBGROUP
  "subgroup(gg%subgroup)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    unfold-defined-constants
    simplify
    (instantiate-existential ("e"))
    simplify
    )))

(def-theorem SINGLETON-E-IS-A-SUBGROUP
  "subgroup(e%subgroup)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    unfold-defined-constants
    simplify-insistently
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    )))


;;; Basic lemmas

(def-theorem SUBGROUPS-ARE-SUBSETS-OF-GG%SUBGROUP
  "forall(a:sets[gg], subgroup(a) implies a subseteq gg%subgroup)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    simplify
    )))

(def-theorem SUBGROUPS-ARE-NONEMPTY
  "forall(a:sets[gg], subgroup(a) implies nonempty_indic_q{a})"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally subgroup)
    simplify
    )))

(def-theorem SUBGROUPS-CLOSED-UNDER-MUL
  "forall(a:sets[gg], subgroup(a) 
    implies 
   forall(g,h:gg, (g in a) and (h in a) implies (g mul h) in a))"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally subgroup)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop, forall(g,h:gg,p))" ("g" "h"))
    )))

(def-theorem SUBGROUPS-CLOSED-UNDER-INV
  "forall(a:sets[gg], subgroup(a) 
    implies 
   forall(g,h:gg, (g in a) implies inv(g) in a))"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally subgroup)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop, forall(g:gg,p))" ("g"))
    )))
  
(def-theorem SUBGROUPS-CONTAIN-E
  "forall(a:sets[gg], subgroup(a) implies (e in a))"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem subgroups-are-nonempty ("a"))
    (force-substitution "e" "x mul inv(x)" (0))
    (apply-macete-with-minor-premises subgroups-closed-under-mul)
    simplify
    (apply-macete-with-minor-premises subgroups-closed-under-inv)
    simplify
    simplify
    simplify
    )))

(def-compound-macete SUBGROUP-MEMBERSHIP
  (series
   (repeat 
    subgroups-closed-under-mul
    subgroups-closed-under-inv
    subgroups-contain-e)
   simplify))


(def-theorem SUBGROUPS-ARE-GROUPS
  "forall(a:sets[gg], subgroup(a) implies group{a,mul,e,inv})"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises subgroup-membership)
    (apply-macete-with-minor-premises subgroup-membership)
    (apply-macete-with-minor-premises subgroup-membership)
    simplify
    simplify
    simplify
    simplify
    simplify
    )))


;;; The following theory interpretation is another proof that a "subgroup is a group".

(def-theorem GROUPS->SUBGROUP-OBL-1
  "forall(a:sets[gg],
     nonempty_indic_q{a}
      and 
     forall(g,h:gg,g in a and h in a implies (g mul h) in a)
      and 
     forall(g:gg,g in a implies inv(g) in a)
      implies 
     e in a)"
  lemma
  (theory groups)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(a:sets[gg], forall(g,h:gg,g in a and h in a implies (g mul h) in a));" 
     ("x" "inv(x)"))
    (instantiate-universal-antecedent 
     "with(a:sets[gg],forall(g:gg,g in a implies inv(g) in a));" 
     ("x"))
    (incorporate-antecedent "with(x:gg,a:sets[gg],(x mul inv(x)) in a);")
    simplify
    )))

(def-theorem GROUPS->SUBGROUP-OBL-2
  "forall(a:sets[gg],
     nonempty_indic_q{a}
      and 
     forall(g,h:gg,g in a and h in a implies (g mul h) in a)
      and 
     forall(g:gg,g in a implies inv(g) in a)
      implies 
     forall(x:gg,x in a implies if(e in a, x, ?gg)=x))"
  lemma
  (theory groups)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem groups->subgroup-obl-1 ("a"))
    (contrapose "with(a:sets[gg],empty_indic_q{a});")
    auto-instantiate-existential
    simplify
    )))

(def-translation GROUPS->SUBGROUP
  (source groups)
  (target groups)
  (assumptions 
   "with(a:sets[gg], nonempty_indic_q{a})"
   "with(a:sets[gg], forall(g,h:gg, (g in a) and (h in a) implies (g mul h) in a))"
   "with(a:sets[gg], forall(g:gg, (g in a) implies (inv(g) in a)))")
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (gg (indic "with(a:sets[gg], a)")))
  (constant-pairs
   (mul "with(a:sets[gg], lambda(x,y:gg, if((x in a) and (y in a), x mul y, ?gg)))")
   (inv "with(a:sets[gg], lambda(x:gg, if(x in a, inv(x), ?gg)))"))
  force-under-quick-load
  (theory-interpretation-check using-simplification))

