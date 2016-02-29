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


(herald SCHROEDER-BERNSTEIN-LEMMAS)


;;; Easy lemmas

(def-theorem A%EVEN-A%ODD-A%INF-COVER-DOM-OF-F
  "a%even union a%odd union a%inf = dom{f}"
  lemma
  reverse
  (theory schroeder-bernstein-theory)
  (usages transportable-macete)
  (proof
   (
    unfold-defined-constants
    extensionality
    direct-inference
    beta-reduce-repeatedly
    (raise-conditional (0))
    simplify
    (case-split ("#(last%a%index(x_0))"))
    (apply-macete-with-minor-premises natural-numbers-are-even-or-odd)
    simplify
    )))

(def-theorem A%EVEN-A%ODD-DISJOINT
  "a%even disj a%odd"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    unfold-defined-constants
    simplify-insistently
    (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
    simplify
    )))

(def-theorem A%EVEN-A%INF-DISJOINT
  "a%even disj a%inf"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    unfold-defined-constants
    simplify-insistently
    )))

(def-theorem A%ODD-A%INF-DISJOINT
  "a%odd disj a%inf"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    unfold-defined-constants
    simplify-insistently
    )))

(def-theorem RAN-OF-F-IS-B%SEQ-AT-1
  "ran{f}=b%seq(1)"
  lemma
  reverse
  (theory schroeder-bernstein-theory)
  (proof
   (
    (unfold-single-defined-constant-globally b%seq)
    simplify
    (unfold-single-defined-constant-globally a%seq)
    simplify
    )))

(def-theorem A%SEQ-TO-B%SEQ-STEP-BY-F
  "forall(i:nn,x:ind_1, x in a%seq(i) iff f(x) in b%seq(1+i))"
  reverse
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    (unfold-single-defined-constant-globally b%seq)
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x"))
    (instantiate-theorem f-injectiveness ("x" "x_$1"))
    (backchain "with(x_$1,x:ind_1,x=x_$1)")
    )))


;;; Harder lemmas

(def-theorem A%SEQ-B%SEQ-HIERARCHIES-LEMMA
  "forall(i:zz, 
     0<=i 
      implies 
     a%seq(1+i) subseteq a%seq(i) 
      and 
     b%seq(1+i) subseteq b%seq(i))"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    (induction integer-inductor ("i"))
    simplify-insistently
    (unfold-single-defined-constant (0) a%seq)
    simplify
    (unfold-single-defined-constant (2) b%seq)
    simplify
    (apply-macete-with-minor-premises tr%image-is-monotone-wrt-subseteq)
    direct-inference
    )))

(def-theorem A%SEQ-HIERARCHY
  "forall(i,j:nn, i<=j implies a%seq(j) subseteq a%seq(i))"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    (force-substitution 
     "forall(i,j:nn,i<=j implies a%seq(j) subseteq a%seq(i))" 
     "forall(i:zz, 
        forall(j:zz, i<=j 
         implies 
        (#(i,nn) and #(j,nn) implies a%seq(j) subseteq a%seq(i))))" 
     (0))
    (apply-macete-with-minor-premises integer-induction)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, not(p))")
    (weaken (0 2 4))
    (incorporate-antecedent "with(i:zz,#(i,nn))")
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    (cut-with-single-formula "#(t,nn)")
    (instantiate-theorem a%seq-b%seq-hierarchies-lemma ("t"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises nn-in-quasi-sort_h-o-real-arithmetic)
    (force-substitution "t+1" "1+t" (0))
    (apply-macete-with-minor-premises tr%subseteq-transitivity)
    (instantiate-existential ("a%seq(t)"))
    simplify
    (weaken (0 2 4))
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop, forall(i:zz,p))")
    )))

(def-theorem LAST%A%INDEX-TO-LAST%B%INDEX-STEP-BY-F
  "forall(x:ind_1, last%b%index(f(x)) == (1 + last%a%index(x)))"
  lemma
  (theory schroeder-bernstein-theory)
  (proof				; 116 nodes
   (
    unfold-defined-constants
    insistent-direct-inference-strategy
    (antecedent-inference "with(p,q:prop, p or q)")
    (eliminate-defined-iota-expression 0 w)
    (cut-with-single-formula "#([-1]+w,nn)")
    (eliminate-iota 0)
    (instantiate-existential ("[-1]+w"))
    (incorporate-antecedent "with(x:ind_2,a:sets[ind_2], x in a)")
    (apply-macete-with-minor-premises tr%membership-in-diff)
    (apply-macete-with-minor-premises a%seq-to-b%seq-step-by-f)
    simplify
    (instantiate-universal-antecedent "with(p:prop,forall(w_1:nn,p))" ("1+z%iota_$0"))
    (contrapose "with(p:prop, not(p))")
    (weaken (0 2 3 4 5))
    (incorporate-antecedent "with(x:ind_1,a:sets[ind_1], x in a)")
    (apply-macete-with-minor-premises tr%membership-in-diff)
    (apply-macete-with-minor-premises a%seq-to-b%seq-step-by-f)
    (weaken (1 2 3 4 5))
    simplify
    simplify
    (cut-with-single-formula "w=0 or 0<w")
    (antecedent-inference "with(p,q:prop, p or q)")
    (contrapose "with(x:ind_2,a:sets[ind_2], x in a)")
    (backchain "with(w:nn,w=0)")
    (unfold-single-defined-constant (0) b%seq)
    simplify
    (weaken (0 1 2 3))
    (apply-macete-with-minor-premises rev%ran-of-f-is-b%seq-at-1)
    (apply-macete-with-minor-premises range-domain-membership)
    (apply-macete-with-minor-premises domain-membership-iff-defined)
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    simplify
    (eliminate-defined-iota-expression 1 w)
    (eliminate-iota 0)
    (instantiate-existential ("1+w"))
    (incorporate-antecedent "with(x:ind_1,a:sets[ind_1], x in a)")
    (apply-macete-with-minor-premises tr%membership-in-diff)
    (apply-macete-with-minor-premises a%seq-to-b%seq-step-by-f)
    (cut-with-single-formula "#([-1]+z%iota_$0,nn)")
    (instantiate-universal-antecedent "with(p:prop,forall(w_1:nn,p))" ("[-1]+z%iota_$0"))
    (contrapose "with(p:prop, not(p))")
    (weaken (0 3 4 5))
    (incorporate-antecedent "with(x:ind_2,a:sets[ind_2], x in a)")
    (apply-macete-with-minor-premises tr%membership-in-diff)
    (apply-macete-with-minor-premises a%seq-to-b%seq-step-by-f)
    simplify
    simplify
    (cut-with-single-formula "z%iota_$0=0 or 0<z%iota_$0")
    (antecedent-inference "with(p,q:prop, p or q)")
    (contrapose "with(x:ind_2,a:sets[ind_2], x in a)")
    (backchain "with(w:nn,z%iota_$0=0)")
    (unfold-single-defined-constant (0) b%seq)
    simplify
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    simplify
    )))

(def-theorem B%ODD-SUBSETEQ-OF-RAN-OF-F
  "b%odd subseteq ran{f}"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    (apply-macete-with-minor-premises ran-of-f-is-b%seq-at-1)
    (unfold-single-defined-constant-globally b%odd)
    (unfold-single-defined-constant-globally last%b%index)
    insistent-direct-inference
    simplify
    direct-inference
    (cut-with-single-formula 
     "#(iota(i_$0:nn, x_$0 in b%seq(i_$0) and not(x_$0 in b%seq(1+i_$0))))")
    (incorporate-antecedent "with(m:nn, odd(m))")
    (eliminate-defined-iota-expression 0 w)
    direct-inference
    (cut-with-single-formula "1<=w")
    (instantiate-transported-theorem 
     a%seq-hierarchy 
     schroeder-bernstein-symmetry 
     ("1" "w"))
    (instantiate-universal-antecedent "with(a,b:sets[ind_2], a subseteq b)" ("x_$0"))
    (case-split ("0=w"))
    (contrapose "with(w:nn,odd(w))")
    (backchain-backwards "with(w:nn,0=w)")
    (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
    (unfold-single-defined-constant-globally even)
    simplify
    simplify
    )))

(def-theorem B%INF-SUBSETEQ-OF-RAN-OF-F
  "b%inf subseteq ran{f}"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    (apply-macete-with-minor-premises ran-of-f-is-b%seq-at-1)
    insistent-direct-inference
    (unfold-single-defined-constant-globally b%inf)
    (unfold-single-defined-constant-globally last%b%index)
    simplify
    direct-inference
    (cut-with-single-formula "x_$0 in (b%seq(0) diff b%seq(1)) or x_$0 in b%seq(1)")
    (antecedent-inference "with(p,q:prop, p or q)")
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    (instantiate-existential ("0"))
    simplify
    (incorporate-antecedent "with(x_$0:ind_2,x_$0 in b%seq(0) diff b%seq(1))")
    (apply-macete-with-minor-premises tr%membership-in-diff)
    direct-and-antecedent-inference-strategy
    simplify
    (cut-with-single-formula "j=0 or 1<=j")
    (antecedent-inference "with(p,q:prop, p or q)")
    (instantiate-transported-theorem 
     a%seq-hierarchy 
     schroeder-bernstein-symmetry 
     ("1" "j"))
    (instantiate-universal-antecedent "with(j:nn,b%seq(j) subseteq b%seq(1))" ("x_$0"))
    simplify
    (apply-macete-with-minor-premises tr%membership-in-diff)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, not(p))")
    (unfold-single-defined-constant-globally b%seq)
    simplify
    )))

(def-theorem IMAGE-OF-A%EVEN-UNDER-F
  "image{f,a%even}=b%odd"
  lemma
  reverse
  (theory schroeder-bernstein-theory)
  (usages transportable-macete)
  (proof
   (
    unfold-defined-constants
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-inference
    insistent-direct-inference
    simplify
    direct-and-antecedent-inference-strategy
    (backchain "with(x,y:ind_2, x=y)")
    (incorporate-antecedent "with(x:ind_1,even(last%a%index(x)))")
    (apply-macete-with-minor-premises last%a%index-to-last%b%index-step-by-f)
    (apply-macete-with-minor-premises even-iff-suc-is-odd)
    simplify
    (weaken (0))
    insistent-direct-inference
    simplify
    (instantiate-theorem b%odd-subseteq-of-ran-of-f ("x_$1"))
    (incorporate-antecedent "with(p:prop, not(p))")
    (unfold-single-defined-constant-globally b%odd)
    simplify
    (incorporate-antecedent "with(p:prop, p)")
    simplify
    direct-inference
    (antecedent-inference "with(p:prop, forsome(x:ind_1,p))")
    (backchain "with(x,y:ind_2, x=y)")
    (apply-macete-with-minor-premises last%a%index-to-last%b%index-step-by-f)
    direct-inference
    auto-instantiate-existential
    (apply-macete-with-minor-premises even-iff-suc-is-odd)
    simplify
    )))

(def-theorem IMAGE-OF-A%ODD-UNDER-INVERSE-OF-G
  "image{inverse{g},a%odd}=b%even"
  lemma
  reverse
  (theory schroeder-bernstein-theory)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises tr%image-under-inverse-of-injective-mapping)
    (apply-macete-with-minor-premises g-injectiveness)
    (apply-macete-with-minor-premises tr%image-of-a%even-under-f)
    direct-inference
    (apply-macete-with-minor-premises tr%rev%a%even-a%odd-a%inf-cover-dom-of-f)
    simplify-insistently
    )))

(def-theorem IMAGE-OF-A%INF-UNDER-F
  "image{f,a%inf}=b%inf"
  lemma
  reverse
  (theory schroeder-bernstein-theory)
  (usages transportable-macete)
  (proof
   (
    unfold-defined-constants
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-inference
    insistent-direct-inference
    simplify
    direct-and-antecedent-inference-strategy
    (backchain "with(x,y:ind_2, x=y)")
    (apply-macete-with-minor-premises last%a%index-to-last%b%index-step-by-f)
    simplify
    (weaken (0))
    insistent-direct-inference
    simplify
    (instantiate-theorem b%inf-subseteq-of-ran-of-f ("x_$1"))
    (incorporate-antecedent "with(p:prop, not(p))")
    (unfold-single-defined-constant-globally b%inf)
    simplify
    (incorporate-antecedent "with(p:prop, p)")
    simplify
    direct-inference
    (antecedent-inference "with(p:prop, forsome(x:ind_1,p))")
    (backchain "with(x,y:ind_2, x=y)")
    (apply-macete-with-minor-premises last%a%index-to-last%b%index-step-by-f)
    direct-inference
    auto-instantiate-existential
    (simplify-antecedent "with(p:prop, not(p))")
    )))


;;; H is a bijection

(def-theorem H-INJECTIVENESS-LEMMA
  "forall(x_1,x_2:ind_1,
     (x_1 in a%inf or x_1 in a%even)
      and 
     f(x_1)=iota(y:ind_2,g(y)=x_2)
      and 
     not(x_2 in a%inf or x_2 in a%even)
      implies 
     x_1=x_2)"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "x_2 in a%odd")
    (cut-with-single-formula "f(x_1) in b%inf")
    (cut-with-single-formula "f(x_1) in b%even")
    (instantiate-transported-theorem 
     a%even-a%inf-disjoint 
     schroeder-bernstein-symmetry 
     ("f(x_1)"))
    (apply-macete-with-minor-premises rev%image-of-a%odd-under-inverse-of-g)
    (weaken (0 2 4))
    simplify
    auto-instantiate-existential
    (apply-macete-with-minor-premises rev%image-of-a%inf-under-f)
    (weaken (0 3))
    simplify
    auto-instantiate-existential
    (weaken (0 1))
    (assume-theorem a%even-a%odd-a%inf-cover-dom-of-f)
    (contrapose "a%even union a%odd union a%inf=dom{f}")
    extensionality
    (instantiate-existential ("x_2"))
    simplify
    (cut-with-single-formula "x_2 in a%odd")
    (cut-with-single-formula "f(x_1) in b%odd")
    (cut-with-single-formula "f(x_1) in b%even")
    (instantiate-transported-theorem 
     a%even-a%odd-disjoint 
     schroeder-bernstein-symmetry 
     ("f(x_1)"))
    (apply-macete-with-minor-premises rev%image-of-a%odd-under-inverse-of-g)
    (weaken (0 2 4))
    (apply-macete-with-minor-premises rev%image-of-a%even-under-f)
    (weaken (0 3))
    simplify
    auto-instantiate-existential
    (weaken (0 1))
    )))

(def-theorem H-INJECTIVENESS
  "injective_q{h}"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    (unfold-single-defined-constant-globally h)
    insistent-direct-inference
    beta-reduce-repeatedly
    (raise-conditional (0))
    (raise-conditional (0))
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (instantiate-theorem f-injectiveness ("x_1" "x_2"))
    (instantiate-theorem f-injectiveness ("x_1" "x_2"))
    (instantiate-theorem f-injectiveness ("x_1" "x_2"))
    (instantiate-theorem f-injectiveness ("x_1" "x_2"))
    (apply-macete-with-minor-premises h-injectiveness-lemma)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises h-injectiveness-lemma)
    direct-and-antecedent-inference-strategy
    (force-substitution "x_1=x_2" "x_2=x_1" (0))
    (apply-macete-with-minor-premises h-injectiveness-lemma)
    direct-and-antecedent-inference-strategy
    (weaken (0 1 2))
    simplify
    (force-substitution "x_1=x_2" "x_2=x_1" (0))
    (apply-macete-with-minor-premises h-injectiveness-lemma)
    direct-and-antecedent-inference-strategy
    (instantiate-transported-theorem inverse-is-injective () ("g"))
    (backchain "injective_q{inverse{g}}")
    simplify
    )))

(def-theorem DOM-OF-H
  "total_q{dom{h},sets[ind_1]}"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    (unfold-single-defined-constant-globally h)
    insistent-direct-inference
    simplify
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "x_0 in a%odd")
    (instantiate-transported-theorem 
     b%odd-subseteq-of-ran-of-f 
     schroeder-bernstein-symmetry 
     ("x_0"))
    (incorporate-antecedent "with(x_0:ind_1,x_0 in ran{g})")
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises eliminate-iota-macete)
    (instantiate-existential ("x"))
    (instantiate-theorem g-injectiveness ("j" "x"))
    (assume-theorem a%even-a%odd-a%inf-cover-dom-of-f)
    (contrapose "a%even union a%odd union a%inf=dom{f}")
    extensionality
    (instantiate-existential ("x_0"))
    simplify
    )))

(def-theorem RAN-OF-H-LEMMA-1
  "forall(x_0:ind_2,
     x_0 in b%inf
      implies
     forsome(x:ind_1,
       x_0
       =if(x in a%inf or x in a%even,
          f(x),
          iota(y:ind_2,g(y)=x))))"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem b%inf-subseteq-of-ran-of-f ("x_0"))
    (contrapose "with(x_0:ind_2,x_0 in ran{f})")
    simplify
    direct-inference
    (contrapose "with(p:prop, forall(x:ind_1,p))")
    (instantiate-existential ("inverse{f}(x_0)"))
    (cut-with-single-formula "inverse{f}(x_0) in a%inf")
    (incorporate-antecedent "with(x_0:ind_2,inverse{f}(x_0) in a%inf)")
    (raise-conditional (0))
    simplify
    direct-inference
    (eliminate-defined-iota-expression 0 w)
    (contrapose "with(x_0:ind_2,x_0 in b%inf)")
    (apply-macete-with-minor-premises rev%image-of-a%inf-under-f)
    simplify
    direct-and-antecedent-inference-strategy
    (contrapose "with(x_0:ind_2,not(inverse{f}(x_0) in a%inf))")
    simplify
    (eliminate-iota 0)
    (instantiate-existential ("x_$0"))
    (instantiate-theorem f-injectiveness ("z%iota" "x_$0"))
    (eliminate-iota 0)
    (instantiate-existential ("x"))
    (instantiate-theorem f-injectiveness ("z%iota" "x"))
    )))

(def-theorem RAN-OF-H-LEMMA-2
  "forall(x_0:ind_2,
     x_0 in b%odd
      implies
     forsome(x:ind_1,
       x_0
       =if(x in a%inf or x in a%even,
          f(x),
          iota(y:ind_2,g(y)=x))))"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem b%odd-subseteq-of-ran-of-f ("x_0"))
    (contrapose "with(x_0:ind_2,x_0 in ran{f})")
    simplify
    direct-inference
    (contrapose "with(p:prop, forall(x:ind_1,p))")
    (instantiate-existential ("inverse{f}(x_0)"))
    (cut-with-single-formula "inverse{f}(x_0) in a%even")
    (incorporate-antecedent "with(x_0:ind_2,inverse{f}(x_0) in a%even);")
    (raise-conditional (0))
    simplify
    direct-inference
    (eliminate-defined-iota-expression 0 w)
    (contrapose "with(x_0:ind_2,x_0 in b%odd);")
    (apply-macete-with-minor-premises rev%image-of-a%even-under-f)
    simplify
    direct-and-antecedent-inference-strategy
    (contrapose "with(x_0:ind_2,not(inverse{f}(x_0) in a%even));")
    simplify
    (eliminate-iota 0)
    (instantiate-existential ("x_$0"))
    (instantiate-theorem f-injectiveness ("z%iota" "x_$0"))
    (eliminate-iota 0)
    (instantiate-existential ("x"))
    (instantiate-theorem f-injectiveness ("z%iota" "x"))
    )))

(def-theorem RAN-OF-H-LEMMA-3
  "forall(x_0:ind_2,
     x_0 in b%even
      implies
     forsome(x:ind_1,
       x_0
       =if(x in a%inf or x in a%even,
          f(x),
          iota(y:ind_2,g(y)=x))))"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("g(x_0)"))
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (contrapose "with(x_0:ind_2,g(x_0) in a%inf)")
    (apply-macete-with-minor-premises tr%rev%image-of-a%inf-under-f)
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-theorem g-injectiveness ("x_0" "x"))
    (instantiate-transported-theorem 
     a%even-a%inf-disjoint 
     schroeder-bernstein-symmetry 
     ("x"))
    (simplify-antecedent "with(x:ind_2,not(x in b%even))")
    (assume-transported-theorem image-of-a%even-under-f schroeder-bernstein-symmetry)
    (contrapose "image{g,b%even}=a%odd")
    extensionality
    (instantiate-existential ("g(x_0)"))
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop, forall(x:ind_2,p))" ("x_0"))
    (raise-conditional (0))
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-theorem a%even-a%odd-disjoint ("g(x_0)"))
    (simplify-antecedent "with(x_0:ind_2,not(g(x_0) in a%odd))")
    (instantiate-theorem a%even-a%odd-disjoint ("g(x_0)"))
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (instantiate-theorem g-injectiveness ("b" "x_0"))
    )))

(def-theorem RAN-OF-H
  "total_q{ran{h},sets[ind_2]}"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    (unfold-single-defined-constant-globally h)
    insistent-direct-inference
    simplify
    (cut-with-single-formula "x_0 in b%inf or x_0 in b%odd or x_0 in b%even")
    (antecedent-inference "with(p,q,r:prop, p or q or r)")
    (apply-macete-with-minor-premises ran-of-h-lemma-1)
    (apply-macete-with-minor-premises ran-of-h-lemma-2)
    (apply-macete-with-minor-premises ran-of-h-lemma-3)
    (assume-transported-theorem 
     a%even-a%odd-a%inf-cover-dom-of-f 
     schroeder-bernstein-symmetry)
    (contrapose "b%even union b%odd union b%inf=dom{g}")
    extensionality
    (instantiate-existential ("x_0"))
    simplify
    )))

(def-theorem H-SURJECTIVENESS
  "surjective_q{h}"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    insistent-direct-inference
    (apply-macete-with-minor-premises dom-of-h)
    (apply-macete-with-minor-premises ran-of-h)
    )))

(def-theorem H-BIJECTIVENESS		; First proved by R. Givan
  "bijective_q{h}"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    insistent-direct-inference
    (apply-macete-with-minor-premises h-surjectiveness)
    (apply-macete-with-minor-premises h-injectiveness)
    )))



