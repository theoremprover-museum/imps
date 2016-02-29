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


(herald equin-finite-cardinals)

;;; This file contains the lemmas needed to prove the 
;;; EQUINUMEROUS-FINITE-CARDINALS lemma


(def-theorem EQUINUMEROUS-FINITE-CARDINALS-LEMMA-1
  "forall(m,n:nn,f:[nn,nn],
     bijective_on_q{f,omega(m+1),omega(n+1)}
      implies
     #(iota(x_0:nn,f(x_0)=n)) and #(f(m)))"
  lemma
  (theory h-o-real-arithmetic)
  (proof				; 51 nodes
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises eliminate-iota-macete)
    (contrapose "with(f:[nn,nn],a:sets[nn], ran{f}=a)")
    extensionality
    (instantiate-existential ("n"))
    beta-reduce-repeatedly
    (raise-conditional (0))
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (contrapose "with(p:prop, forall(i:nn,p))")
    (antecedent-inference-strategy (0))
    (simplify-antecedent "with(n:nn,not(n<n+1));")
    (instantiate-existential ("x_$1"))
    (backchain "with(f:[nn,nn],a:sets[nn], injective_on_q{f,a})")
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    direct-inference
    (apply-macete-with-minor-premises rev%finite-cardinal-members-are-<)
    (force-substitution "omega(m+1)" "dom{f}" (0))
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    simplify
    (apply-macete-with-minor-premises rev%finite-cardinal-members-are-<)
    (force-substitution "omega(m+1)" "dom{f}" (0))
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    (contrapose "with(n:nn,?unit%sort=omega(n+1)(n));")
    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
    (force-substitution "dom{f}" "omega(m+1)" (0))
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    simplify
    )))

(def-theorem EQUINUMEROUS-FINITE-CARDINALS-LEMMA-2
  "forall(m,n:nn,f:[nn,nn],
     bijective_on_q{f,omega(m+1),omega(n+1)}
      implies
     dom{lambda(x:nn,if(x<m,if(x=iota(x_0:nn,f(x_0)=n), f(m), f(x)),?nn))}
     = omega(m))"
  lemma
  (theory h-o-real-arithmetic)
  (proof				; 37 nodes
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(iota(x_0:nn,f(x_0)=n)) and #(f(m))")
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-inference
    insistent-direct-inference
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    beta-reduce-insistently
    (raise-conditional (0))
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (weaken (0))
    insistent-direct-inference
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    beta-reduce-repeatedly
    (raise-conditional (0))
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
    (force-substitution "dom{f}" "omega(m+1)" (0))
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (weaken (0 2 3 4 5))
    simplify
    (apply-macete-with-minor-premises equinumerous-finite-cardinals-lemma-1)
    simplify
    )))

(def-theorem EQUINUMEROUS-FINITE-CARDINALS-LEMMA-3A
  "forall(m,n:nn,f:[nn,nn],
     bijective_on_q{f,omega(m+1),omega(n+1)}
      implies
     ran{lambda(x:nn,if(x<m,if(x=iota(x_0:nn,f(x_0)=n), f(m), f(x)),?nn))}
      subseteq 
     omega(n))"
  lemma
  (theory h-o-real-arithmetic)
  (proof				; 108 nodes
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(iota(x_0:nn,f(x_0)=n)) and #(f(m))")
    insistent-direct-inference
    beta-reduce-insistently
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (force-substitution "x_$0" "if(x_$1<m,
     if(x_$1=iota(x_0:nn,f(x_0)=n), f(m), f(x_$1)),
     ?nn)" (0))
    (raise-conditional (0))
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(n:nn,p:prop, n=iota(x_0:nn,p))")
    (eliminate-defined-iota-expression 0 u)
    direct-inference
    (instantiate-universal-antecedent "with(p:prop, forall(u_1:nn,p))" ("m"))
    (cut-with-single-formula "f(m) in ran{f}")
    (contrapose "with(m:nn,f:[nn,nn],f(m) in ran{f})")
    (force-substitution "ran{f}" "omega(n+1)" (0))
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (weaken (2 3 4 5 6 7 8 9 10))
    (contrapose "with(n,m:nn,f:[nn,nn],not(f(m)=n))")
    simplify
    (apply-macete-with-minor-premises tr%range-domain-membership)
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    (contrapose "with(u,x_$1:nn,x_$1=u)")
    (weaken (0 1 4 5 6 7 8 9))
    simplify
    (contrapose "with(n:nn,f:[nn,nn],x_$1:nn,not(x_$1=iota(x_0:nn,f(x_0)=n)))")
    (eliminate-defined-iota-expression 0 u)
    (instantiate-universal-antecedent "with(p:prop, forall(u_1:nn,p))" ("x_$1"))
    (cut-with-single-formula "#(f(x_$1))")
    (cut-with-single-formula "f(x_$1) in ran{f}")
    (incorporate-antecedent "with(x_$1:nn,f:[nn,nn],f(x_$1) in ran{f})")
    (force-substitution "ran{f}" "omega(n+1)" (0))
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (weaken (2 4 5 6 7 8 9 10))
    simplify
    (apply-macete-with-minor-premises tr%range-domain-membership)
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
    (force-substitution "dom{f}" "omega(m+1)" (0))
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (weaken (0 1 2 4 5 6 7 8 9))
    simplify
    (contrapose "with(m,n:nn, m=n)")
    (raise-conditional (0))
    (raise-conditional (0))
    (contrapose "with(m,x_$1:nn,not(x_$1<m))")
    (antecedent-inference-strategy (0))
    (simplify-antecedent "with(x_$2:nn,x_$2=?nn)")
    (apply-macete-with-minor-premises equinumerous-finite-cardinals-lemma-1)
    simplify
    )))

(def-theorem EQUINUMEROUS-FINITE-CARDINALS-LEMMA-3B
  "forall(m,n:nn,f:[nn,nn],
     bijective_on_q{f,omega(m+1),omega(n+1)}
      implies
     omega(n) 
      subseteq 
     ran{lambda(x:nn,if(x<m,if(x=iota(x_0:nn,f(x_0)=n), f(m), f(x)),?nn))})"
  lemma
  (theory h-o-real-arithmetic)
  (proof				; 122 nodes
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(iota(x_0:nn,f(x_0)=n)) and #(f(m))")
    insistent-direct-inference
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    beta-reduce-insistently
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, not(p))")
    (cut-with-single-formula "x_$0 in ran{f}")
    (incorporate-antecedent "with(x_$0:nn,f:[nn,nn],x_$1 in ran{f})")
    beta-reduce-insistently
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("if(x_$0=f(m),iota(x_0:nn,f(x_0)=n),x)"))
    (raise-conditional (0))
    (raise-conditional (0))
    (raise-conditional (0))
    (raise-conditional (0))
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (contrapose "with(n:nn,f:[nn,nn],x:nn,x=iota(x_0:nn,f(x_0)=n))")
    (eliminate-defined-iota-expression 0 u)
    (contrapose "with(x:nn,f:[nn,nn],x_$0:nn,x_$0=f(x))")
    (weaken (1 2 3 5 6 8 9 10 11))
    simplify
    (contrapose "with(p:prop, not(p))")
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, not(p))")
    direct-and-antecedent-inference-strategy
    (eliminate-defined-iota-expression 0 u)
    (cut-with-single-formula "u<m or u=m or m<u")
    (antecedent-inference "with(p,q,r:prop, p or q or r)")
    (contrapose "with(n,u:nn,f:[nn,nn],f(u)=n)")
    (weaken (0 1 4 5 6 7 9 10 11 12))
    simplify
    (cut-with-single-formula "u<m+1")
    (contrapose "with(m,u:nn,u<m+1)")
    (weaken (2 3 4 5 6 7 8 9 10 11 12 13))
    simplify
    (apply-macete-with-minor-premises rev%finite-cardinal-members-are-<)
    (force-substitution "omega(m+1)" "dom{f}" (0))
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    simplify
    (weaken (0 1 2 3 4 5 6 7 8 9 10 11))
    simplify
    (cut-with-single-formula "x<m or x=m or m<x")
    (antecedent-inference "with(p,q,r:prop, p or q or r)")
    (contrapose "with(m:nn,f:[nn,nn],x_$0:nn,not(x_$0=f(m)))")
    (weaken (0 2 4 5 6 7 8 9 10))
    simplify
    (cut-with-single-formula "x<m+1")
    (contrapose "with(m,x:nn,x<m+1)")
    (weaken (2 3 4 5 6 7 8 9 10 11))
    simplify
    (apply-macete-with-minor-premises rev%finite-cardinal-members-are-<)
    (force-substitution "omega(m+1)" "dom{f}" (0))
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    simplify
    (weaken (0 1 2 3 4 5 6 7 8 9))
    simplify
    (force-substitution "ran{f}" "omega(n+1)" (0))
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (weaken (0 2 3 4 5))
    simplify
    (apply-macete-with-minor-premises equinumerous-finite-cardinals-lemma-1)
    simplify
    )))

(def-theorem EQUINUMEROUS-FINITE-CARDINALS-LEMMA-3
  "forall(m,n:nn,f:[nn,nn],
     bijective_on_q{f,omega(m+1),omega(n+1)}
      implies
     ran{lambda(x:nn,if(x<m,if(x=iota(x_0:nn,f(x_0)=n), f(m), f(x)),?nn))}
     = omega(n))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    (apply-macete-with-minor-premises equinumerous-finite-cardinals-lemma-3a)
    (apply-macete-with-minor-premises equinumerous-finite-cardinals-lemma-3b)
    direct-and-antecedent-inference-strategy
    )))

(def-theorem EQUINUMEROUS-FINITE-CARDINALS-LEMMA-4
  "forall(m,n:nn,f:[nn,nn],
     bijective_on_q{f,omega(m+1),omega(n+1)}
      implies
     injective_on_q{lambda(x:nn,
       if(x<m,if(x=iota(x_0:nn,f(x_0)=n), f(m), f(x)),?nn)),omega(m)})"
  lemma
  (theory h-o-real-arithmetic)
  (proof				; 74 nodes
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (backchain "with(f:[nn,nn],m:nn,injective_on_q{f,omega(m+1)})")
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(x_$0,m:nn,x_$0 in omega(m))")
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (weaken (0 1 2 3 4))
    simplify
    (incorporate-antecedent "with(x_$1,m:nn,x_$1 in omega(m))")
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (weaken (0 1 2 3 4 5))
    simplify
    (cut-with-single-formula "#(f(x_$0)) and #(f(x_$1))")
    (weaken (1 2))
    (incorporate-antecedent "with(m,n:nn, m=n)")
    (apply-macete-with-minor-premises rev%finite-cardinal-members-are-<)
    simplify
    (raise-conditional (0))
    (raise-conditional (0))
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(f:[nn,nn],a:sets[nn],injective_on_q{f,a})" ("m" "x_$1"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    simplify
    (contrapose "with(p:prop, not(p))")
    (incorporate-antecedent "with(x_$1,m:nn,x_$1 in omega(m))")
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (contrapose "with(x_$1,m:nn,x_$1 in omega(m));")
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    simplify
    (instantiate-universal-antecedent 
     "with(f:[nn,nn],a:sets[nn],injective_on_q{f,a})" ("m" "x_$0"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    simplify
    (contrapose "with(x_$0,m:nn,not(x_$0 in omega(m+1)))")
    (incorporate-antecedent "with(x_$0,m:nn,x_$0 in omega(m))")
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (contrapose "with(x_$1,m:nn,x_$0 in omega(m));")
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    simplify
    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
    (force-substitution "dom{f}" "omega(m+1)" (0 1))
    simplify
    )))

(def-theorem EQUINUMEROUS-FINITE-CARDINALS-LEMMA-5
  "forall(m,n:nn, 
     omega(m+1) equinumerous omega(n+1)
      implies
     omega(m) equinumerous omega(n))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential 
     ("lambda(x:nn,if(x<m,if(x=iota(x_0:nn,f(x_0)=n),f(m),f(x)),?nn))"))
    insistent-direct-inference
    insistent-direct-inference
    (apply-macete-with-minor-premises equinumerous-finite-cardinals-lemma-2)
    (apply-macete-with-minor-premises equinumerous-finite-cardinals-lemma-3)
    (apply-macete-with-minor-premises equinumerous-finite-cardinals-lemma-4)
    simplify
    )))

(def-theorem EQUINUMEROUS-FINITE-CARDINALS-LEMMA-6
  "forall(n:zz, 
     0<=n 
      implies 
     forall(m:nn, omega(m) equinumerous omega(n) implies m<=n))"
  lemma
  (theory h-o-real-arithmetic)
  (proof				; 34 nodes
   (
    (apply-macete-with-minor-premises integer-induction)
    beta-reduce-repeatedly
    direct-inference
    (apply-macete-with-minor-premises omega-0-is-empty-indicator)
    (apply-macete-with-minor-premises tr%equinumerous-to-empty-indic)
    (apply-macete-with-minor-premises rev%omega-0-is-empty-indicator)
    (unfold-single-defined-constant-globally omega)
    direct-and-antecedent-inference-strategy
    (contrapose "with(a,b:sets[nn], a = b)")
    extensionality
    (instantiate-existential ("0"))
    simplify
    (weaken (0))
    direct-inference-strategy
    (cut-with-single-formula "m=0 or 0<m")
    (antecedent-inference "with(p,q:prop, p or q)")
    simplify
    (force-substitution "m<=t+1" "m-1<=t" (0))
    (backchain "with(p:prop, forall(m:nn, p))")
    (apply-macete-with-minor-premises equinumerous-finite-cardinals-lemma-5)
    (force-substitution "m-1+1" "m" (0))
    simplify
    simplify
    simplify
    simplify)))

