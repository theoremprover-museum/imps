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


(herald schroeder-bernstein-theorem)


(include-files
  (files (imps theories/cardinality/cardinality)))



(def-language SCHROEDER-BERNSTEIN-LANGUAGE
  (embedded-language generic-theory-2)
  (constants
    (f "[ind_1,ind_2]")
    (g "[ind_2,ind_1]")))

(def-theory SCHROEDER-BERNSTEIN-THEORY
  (language schroeder-bernstein-language)
  (component-theories generic-theory-2)
  (axioms
   (f-totality "total_q{f,[ind_1,ind_2]}" d-r-convergence)
   (g-totality "total_q{g,[ind_2,ind_1]}" d-r-convergence)
   (f-injectiveness "injective_q{f}")
   (g-injectiveness "injective_q{g}")))


;;; A%SEQ/B%SEQ DEFINITION

(def-recursive-constant (A%SEQ B%SEQ)
  ("lambda(a%seq_0:[nn,sets[ind_1]],b%seq_0:[nn,sets[ind_2]],
      lambda(i:nn,
        if(i=0, 
           dom{f},
           lambda(dummy:sets[ind_2],
             if(#(dummy), image{g, dummy}, ?[ind_1,unit%sort]))
           (b%seq_0(i-1)))))"
   "lambda(a%seq_0:[nn,sets[ind_1]],b%seq_0:[nn,sets[ind_2]],
      lambda(i:nn,
        if(i=0, 
           dom{g},
           lambda(dummy:sets[ind_1],
             if(#(dummy), image{f, dummy}, ?[ind_2,unit%sort]))
           (a%seq_0(i-1)))))")
 (theory schroeder-bernstein-theory)
 (definition-name schroeder-bernstein-set-functions))


;;; OBLIGATIONS

(include-files
  (files (imps theories/cardinality/schroeder-bernstein-obligations)))


;;; SCHROEDER-BERNSTEIN SYMMETRY

(def-translation SCHROEDER-BERNSTEIN-SYMMETRY
  (source schroeder-bernstein-theory)
  (target schroeder-bernstein-theory)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (ind_1 ind_2)
   (ind_2 ind_1))
  (constant-pairs
   (f "g")
   (g "f")
   (a%seq "b%seq")
   (b%seq "a%seq"))
  force-under-quick-load)


;;; DEFINITIONS

(def-constant LAST%A%INDEX
  "lambda(x:ind_1, iota(i:nn, x in (a%seq(i) diff a%seq(1+i))))"
  (theory schroeder-bernstein-theory))

(def-constant A%INF
  "indic(x:ind_1, not(#(last%a%index(x))))"
  (theory schroeder-bernstein-theory))

(def-constant A%EVEN
  "indic(x:ind_1, even(last%a%index(x)))"
  (theory schroeder-bernstein-theory))

(def-constant A%ODD
  "indic(x:ind_1, odd(last%a%index(x)))"
  (theory schroeder-bernstein-theory))

(def-renamer SB-RENAMER
  (pairs
   (last%a%index last%b%index)
   (a%inf b%inf)
   (a%even b%even)
   (a%odd b%odd)))

(def-transported-symbols 
  (last%a%index a%inf a%even a%odd)
  (translation schroeder-bernstein-symmetry)
  (renamer sb-renamer))

(def-constant H
  "lambda(x:ind_1, 
     if(x in a%inf or x in a%even,
        f(x),
        inverse(g)(x)))"
  (theory schroeder-bernstein-theory))


;;; PRELIMINARY LEMMAS

(def-theorem A-SEQ-B-SEQ-DEFINEDNESS
  "forall(n:zz, 0<=n implies #(a%seq(n),sets[ind_1]) and #(b%seq(n),sets[ind_2]))"
  lemma
  (theory schroeder-bernstein-theory)
  (proof ((induction integer-inductor ("n")))))

(def-theorem A-SEQ-DEFINEDNESS
  "total_q{a%seq,[nn,sets[ind_1]]}"
  lemma
  (theory schroeder-bernstein-theory)
  (usages d-r-convergence)
  (proof
   (
    insistent-direct-inference
    (instantiate-theorem a-seq-b-seq-definedness ("x_0"))
    (simplify-antecedent "with(x_0:nn,not(0<=x_0))")
    )))

(def-theorem B-SEQ-DEFINEDNESS
  "total_q{b%seq,[nn,sets[ind_2]]}"
  lemma
  (theory schroeder-bernstein-theory)
  (usages d-r-convergence)
  (proof
   (
    insistent-direct-inference
    (instantiate-theorem a-seq-b-seq-definedness ("x_0"))
    (simplify-antecedent "with(x_0:nn,not(0<=x_0))")
    )))


;;; LEMMAS

(include-files
  (files (imps theories/cardinality/schroeder-bernstein-lemmas)))


;;; SCHROEDER-BERNSTEIN GENERALIZATION

(def-translation SCHROEDER-BERNSTEIN->GENERIC-THEORY-2
  (source schroeder-bernstein-theory)
  (target generic-theory-2)
  (fixed-theories h-o-real-arithmetic)
  (assumptions
   "with(a:sets[ind_1],nonempty_indic_q{a})"
   "with(b:sets[ind_2],nonempty_indic_q{b})"
   "with(u:[ind_1,ind_2],a:sets[ind_1],dom{u}=a)"
   "with(v:[ind_2,ind_1],b:sets[ind_2],dom{v}=b)"
   "with(u:[ind_1,ind_2],b:sets[ind_2],ran{u} subseteq b)"
   "with(v:[ind_2,ind_1],a:sets[ind_1],ran{v} subseteq a)"
   "with(u:[ind_1,ind_2],a:sets[ind_1],injective_on_q{u,a})"
   "with(v:[ind_2,ind_1],b:sets[ind_2],injective_on_q{v,b})")
  (sort-pairs
   (ind_1 (indic "with(a:sets[ind_1],a)"))
   (ind_2 (indic "with(b:sets[ind_2],b)")))
  (constant-pairs
   (f "with(u:[ind_1,ind_2],u)")
   (g "with(v:[ind_2,ind_1],v)"))
  dont-enrich
  force-under-quick-load
  (theory-interpretation-check using-simplification))


;;; THE THEOREM

(def-theorem SB-THEOREM-LEMMA-1
  "forsome(h_0:[ind_1,ind_2], bijective_q{h_0})"
  lemma
  (theory generic-theory-2)
  (translation schroeder-bernstein->generic-theory-2)
  (proof
   (
    (assume-theorem h-bijectiveness)
    auto-instantiate-existential
    )))

(def-theorem SB-THEOREM-LEMMA-2
  "forall(a:sets[ind_1], b:sets[ind_2], 
     (a=empty_indic{ind_1} or b=empty_indic{ind_2}) 
       implies
     ((a embeds b) and (b embeds a) implies (a equinumerous b)))"
  lemma
  (theory generic-theory-2)
  (proof
   (
    direct-inference
    direct-inference
    (antecedent-inference "with(p,q:prop, p or q)")
    (force-substitution "a" "empty_indic{ind_1}" (1))
    (apply-macete-with-minor-premises tr%embeds-in-empty-indic)
    direct-inference
    (backchain "with(p,q:prop, p and q)")
    (apply-macete-with-minor-premises equinumerous-to-empty-indic)
    (force-substitution "b" "empty_indic{ind_2}" (0))
    (apply-macete-with-minor-premises embeds-in-empty-indic)
    direct-inference
    (backchain "with(p,q:prop, p and q)")
    (apply-macete-with-minor-premises tr%equinumerous-is-symmetric)
    (apply-macete-with-minor-premises tr%equinumerous-to-empty-indic)
    )))

(def-theorem SCHROEDER-BERNSTEIN-THEOREM
  "forall(a:sets[ind_1], b:sets[ind_2],
     (a embeds b) and (b embeds a) implies (a equinumerous b))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-inference-strategy
    (case-split ("a=empty_indic{ind_1} or b=empty_indic{ind_2}"))
    (apply-macete-with-minor-premises sb-theorem-lemma-2)
    direct-inference
    (antecedent-inference-strategy (1))
    (instantiate-theorem sb-theorem-lemma-1 ("f_$1" "f_$0" "b" "a"))
    (weaken (1 2 3 4 5 6))
    (contrapose "with(p:prop, not(p))")
    (instantiate-transported-theorem equals-empty-indic-iff-empty () ("a"))
    simplify
    (weaken (1 2 3 4 5 6))
    (contrapose "with(p:prop, not(p))")
    (instantiate-transported-theorem equals-empty-indic-iff-empty () ("b"))
    simplify
    (weaken (4 5 6 7 8 9 10))
    (instantiate-existential ("h_0"))
    insistent-direct-and-antecedent-inference-strategy
    (weaken (1 3))
    extensionality
    direct-inference
    (instantiate-universal-antecedent 
     "with(a,b:sets[ind_1],  a subseteq b)" ("x_0"))
    (instantiate-universal-antecedent 
     "with(p:prop, forall(x_$0:ind_1,p))" ("x_0"))
    beta-reduce-repeatedly
    simplify
    (weaken (1))
    (incorporate-antecedent "with(p:prop, p)")
    simplify-insistently
    (weaken (0 2 3))
    extensionality
    direct-inference
    (instantiate-universal-antecedent 
     "with(a,b:sets[ind_2],  a subseteq b)" ("x_0"))
    beta-reduce-repeatedly
    (raise-conditional (0))
    simplify
    direct-inference
    (instantiate-universal-antecedent 
     "with(p:prop, forall(x_$0:ind_1,p))" ("x_$0"))
    (weaken (1 2))
    simplify
    (contrapose "with(p:prop, not(p))")
    simplify
    (weaken (1 2))
    (weaken (1))
    (incorporate-antecedent "with(p:prop, p)")
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (raise-conditional (0))
    simplify
    auto-instantiate-existential
    (weaken (0 1 5 7 8))
    (backchain "with(p:prop, forall(x_1,x_2:ind_1,p))")
    direct-and-antecedent-inference-strategy
    )))

