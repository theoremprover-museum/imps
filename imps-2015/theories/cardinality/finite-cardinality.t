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


(herald finite-cardinality)


(include-files
  (files (imps theories/cardinality/cardinality)))



;;; Parsing and printing

(def-parse-syntax finite-cardinality
  (token f_card)
  (null-method prefix-operator-method) 
  (binding 160))

(def-parse-syntax finite-indicator? 
  (token f_indic_q)
  (null-method prefix-operator-method) 
  (binding 160))

;; This was changed Thu May 20 16:30:25 EDT 1993 by JT. Previous parsing and printing
;; were wrong.

(def-parse-syntax finite-sort?
  (token f_sort_q)
  (null-method prefix-sort-dependent-operator-method) 
  (binding 160))

(def-print-syntax finite-cardinality
  (token f_card)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax finite-indicator?
  (token f_indic_q)
  (method present-prefix-operator)
  (binding 160))

;; Changed Thu May 20 16:30:25 EDT 1993 by jt

(def-print-syntax finite-sort?
  (token f_sort_q)
  (method present-sort-dependent-prefix-operator)
  (binding 160))

(def-print-syntax finite-cardinality
  tex
  (token (" | " " | "))
  (method present-tex-delimited-expression)
  (binding 80))

(def-print-syntax finite-indicator?
  tex
  (token finite?)
  (method present-loglike-operator)
  (binding 160))

(def-print-syntax finite-sort?
  tex
  (token finite?)
  (method present-loglike-operator)
  (binding 160))


;;; Definition of omega

(def-constant OMEGA
  "lambda(n:nn, indic(m:nn, m<n))"
  (theory h-o-real-arithmetic))


;;; Quasi-constructors

(def-quasi-constructor FINITE-CARDINALITY
  "lambda(a:sets[ind_1], iota(n:nn, a equinumerous omega(n)))"
  (language generic-theory-1)
  (fixed-theories h-o-real-arithmetic))

(def-quasi-constructor FINITE-INDICATOR?
  "lambda(a:sets[ind_1], #(f_card{a}))"
  (language generic-theory-1)
  (fixed-theories h-o-real-arithmetic))

(def-quasi-constructor FINITE-SORT?
  "lambda(e:ind_1, f_indic_q{sort_to_indic{ind_1}})"
  (language generic-theory-1)
  (fixed-theories h-o-real-arithmetic))


;;; Preliminary lemmas

(def-theorem OMEGA-IS-TOTAL
  "total_q(omega,[nn,sets[nn]])"
  (theory h-o-real-arithmetic)
  (usages d-r-convergence)
  (proof
   (
    direct-inference
    insistent-direct-inference
    (unfold-single-defined-constant-globally omega)
    )))

(def-theorem OMEGA-0-IS-EMPTY-INDICATOR
  "omega(0)=empty_indic{nn}"
  reverse
  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant-globally omega)
    extensionality
    direct-inference
    simplify
    )))

(def-theorem OMEGA-1-IS-SINGLETON
  "omega(1)=singleton{0}"
  reverse
  (theory h-o-real-arithmetic)
  (proof
   (
    (force-substitution "singleton{0}" "singleton{iota(z:nn,z=0)}" (0))
    (unfold-single-defined-constant-globally omega)
    extensionality
    direct-inference
    simplify
    (case-split-on-conditionals (0))
    (force-substitution "iota(z:nn,z=0)" "0" (0))
    simplify-insistently
    extensionality
    direct-inference
    simplify
    (case-split-on-conditionals (0))
    )))

(def-theorem FINITE-CARDINAL-MEMBERS-ARE-<
  "forall(m,n:nn, m in omega(n) iff m<n)"
  reverse
  (theory h-o-real-arithmetic)
  (usages rewrite)
  (proof
   (
    (unfold-single-defined-constant-globally omega)
    simplify-insistently
    )))

(def-theorem FINITE-CARDINAL-APPLICATION
  "forall(m,n:nn, m<n implies omega(n)(m) = an%individual)"
  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant-globally omega)
    simplify-insistently
    )))

(def-theorem OMEGA-OF-SUCCESSOR 
  "forall(n:nn, omega(1+n) = omega(n) union singleton{n})"
  (theory h-o-real-arithmetic)
  (proof				; 11 nodes
   (

    simplify-insistently
    direct-inference
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises finite-cardinal-application)
    (apply-macete-with-minor-premises finite-cardinal-application)

    )))


;;; F-CARD vs. EQUINUMEROUS lemmas

(def-theorem F-CARD-EQUAL-IMPLIES-EQUINUMEROUS
  "forall(a:sets[ind_1],b:sets[ind_2], 
     f_card{a} = f_card{b} implies a equinumerous b)"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof				; 51 nodes
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "f_indic_q{a} and f_indic_q{b}")
    (incorporate-antecedent "with(i,j:nn, i = j)")
    (eliminate-defined-iota-expression 0 u)
    (eliminate-defined-iota-expression 0 v)
    direct-inference
    (cut-with-single-formula 
     "(a equinumerous omega(u) and omega(u) equinumerous b) implies a equinumerous b")
    (backchain "with(p,q,r:prop, p and q implies r)")
    direct-inference
    (apply-macete-with-minor-premises tr%equinumerous-is-symmetric)
    simplify
    (instantiate-transported-theorem 
     equinumerous-is-transitive 
     () 
     ("a" "omega(u)" "b"))
    simplify
    )))

(def-theorem FINITE-AND-EQUINUMEROUS-IMPLIES-F-CARD-EQUAL
  "forall(a:sets[ind_1],b:sets[ind_2], 
     f_indic_q{a} and (a equinumerous b) implies f_card{a} = f_card{b})"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof				; 55 nodes
   (
    direct-inference-strategy
    (eliminate-defined-iota-expression 0 u)
    (eliminate-iota 0)
    (instantiate-existential ("u"))
    (cut-with-single-formula 
     "(b equinumerous a and a equinumerous omega(u)) 
       implies 
      b equinumerous omega(u)")
    (backchain "with(p,q,r:prop, p and q implies r)")
    direct-inference
    (apply-macete-with-minor-premises tr%equinumerous-is-symmetric)
    (instantiate-transported-theorem 
     equinumerous-is-transitive 
     () 
     ("b" "a" "omega(u)"))
    (backchain "with(p:prop,forall(u_1:nn,p))")
    (instantiate-existential ("z%iota_$0"))
    (cut-with-single-formula 
     "(a equinumerous b and b equinumerous omega(z%iota_$0)) 
       implies 
      a equinumerous omega(z%iota_$0)")
    (backchain "with(p,q,r:prop, p and q implies r)")
    direct-inference
    (instantiate-transported-theorem 
     equinumerous-is-transitive 
     () 
     ("a" "b" "omega(z%iota_$0)"))
    )))

(def-theorem F-CARD-EQUAL-IFF-FINITE-AND-EQUINUMEROUS
  "forall(a:sets[ind_1],b:sets[ind_2], 
     f_card{a} = f_card{b} 
      iff 
     ((f_indic_q{a} or f_indic_q{b}) and (a equinumerous b)))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-inference-strategy
    (apply-macete-with-minor-premises 
     f-card-equal-implies-equinumerous)
    (antecedent-inference "with(p,q:prop, p and q)")
    (antecedent-inference "with(p,q:prop, p or q)")
    (apply-macete-with-minor-premises 
     finite-and-equinumerous-implies-f-card-equal)
    simplify
    (force-substitution "f_card{a}=f_card{b}" "f_card{b}=f_card{a}" (0))
    (apply-macete-with-minor-premises 
     tr%finite-and-equinumerous-implies-f-card-equal)
    direct-inference
    (apply-macete-with-minor-premises 
     equinumerous-is-symmetric)
    simplify
    )))

(def-theorem EQUINUMEROUS-IMPLIES-F-CARD-QUASI-EQUAL
  "forall(a:sets[ind_1],b:sets[ind_2], 
     a equinumerous b implies f_card{a} == f_card{b})"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises 
     f-card-equal-iff-finite-and-equinumerous)
    simplify
    )))


;;; EQUINUMEROUS-FINITE-CARDINALS lemma

(include-files
  (files (imps theories/cardinality/equin-finite-cardinals)))


(def-theorem EQUINUMEROUS-FINITE-CARDINALS
  "forall(m,n:nn, omega(m) equinumerous omega(n) implies m=n)"
  (theory h-o-real-arithmetic)
  (proof				; 36 nodes
   (
    direct-inference-strategy
    (cut-with-single-formula "omega(n) equinumerous omega(m)")
    (instantiate-theorem equinumerous-finite-cardinals-lemma-6 ("m"))
    (simplify-antecedent "with(m:nn,not(0<=m))")
    (instantiate-universal-antecedent "with(p:prop, forall(m:nn,p))" ("n"))
    (instantiate-theorem equinumerous-finite-cardinals-lemma-6 ("n"))
    (simplify-antecedent "with(m:nn,not(0<=m));")
    (instantiate-universal-antecedent "with(p:prop, forall(m:nn,p))" ("m"))
    simplify
    (apply-macete-with-minor-premises tr%equinumerous-is-symmetric)
    )))


;;; F-CARD lemmas

(def-theorem IOTA-FREE-DEFINITION-OF-F-CARD
  "forall(a:sets[ind_1],n:nn, f_card{a}=n iff a equinumerous omega(n))"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    direct-inference
    (cut-with-single-formula "f_indic_q{a}")
    (incorporate-antecedent "with(n:nn,a:sets[ind_1],f_card{a}=n)")
    (eliminate-defined-iota-expression 0 u)
    direct-inference
    simplify
    (eliminate-iota 0)
    (instantiate-existential ("n"))
    (apply-macete-with-minor-premises equinumerous-finite-cardinals)
    (cut-with-single-formula 
     "omega(z%iota_$0) equinumerous a and a equinumerous omega(n) 
       implies 
      omega(z%iota_$0) equinumerous omega(n)")
    (backchain "with(p,q,r:prop, p and q implies r)")
    direct-inference
    (apply-macete-with-minor-premises tr%equinumerous-is-symmetric)
    (apply-macete-with-minor-premises tr%equinumerous-is-transitive)
    (apply-macete-with-minor-premises tr%equinumerous-is-transitive)
    (instantiate-transported-theorem 
     equinumerous-is-transitive () ("z%iota_$0" "a" "n"))
    (instantiate-transported-theorem 
     equinumerous-is-transitive () ("omega(z%iota_$0)" "a" "omega(n)"))
    )))

(def-theorem IOTA-FREE-DEFINITION-OF-F-INDIC-Q
  "forall(a:sets[ind_1],n:nn, f_indic_q{a} iff forsome(n:nn, f_card{a}=n))"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("f_card{a}"))
    )))

(def-theorem F-CARD-OF-A-FINITE-CARDINAL
  "forall(n:nn, f_card{omega(n)} = n)"
  reverse
  (theory h-o-real-arithmetic)
  (usages rewrite)
  (proof
   (
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-card)
    (apply-macete-with-minor-premises tr%equinumerous-is-reflexive)
    )))

(def-theorem FINITE-CARDINAL-IS-F-INDIC
  "forall(n:nn, f_indic_q{omega(n)})"
  (theory h-o-real-arithmetic)
  (usages rewrite)
  (proof
   (
    direct-inference
    (instantiate-theorem f-card-of-a-finite-cardinal ("n"))
    )))

(def-theorem EMPTY-INDIC-HAS-F-CARD-ZERO
  "forall(a:sets[ind_1], f_card{a}=0 iff a=empty_indic{ind_1})"
  reverse
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises iota-free-definition-of-f-card)
    (apply-macete-with-minor-premises omega-0-is-empty-indicator)
    (apply-macete-with-minor-premises tr%equinumerous-to-empty-indic)
    )))

(def-theorem EMPTY-INDIC-HAS-F-CARD-ZERO-REWRITE
  "f_card{empty_indic{ind_1}}=0"
  (usages transportable-rewrite)
  (theory generic-theory-1)
  (proof ((apply-macete-with-minor-premises empty-indic-has-f-card-zero))))

  

(def-theorem SINGLETON-HAS-F-CARD-ONE-LEMMA-1
  "forall(a:sets[ind_1], f_card{a}=1 implies forsome(y:ind_1, a=singleton{y}))"
  lemma
  (theory generic-theory-1)
  (proof
   (
    (apply-macete-with-minor-premises iota-free-definition-of-f-card)
    direct-inference
    direct-inference
    (cut-with-single-formula "singleton{0} equinumerous a")
    (antecedent-inference "with(a:sets[ind_1],singleton{0} equinumerous a)")
    (instantiate-transported-theorem 
     range-of-bijection-on-singleton 
     () 
     ("f_$0" "singleton{0}" "a"))
    (instantiate-universal-antecedent "with(p:prop, forall(x_$5:zz,p))" ("0"))
    (simplify-antecedent "not(singleton{0}=singleton{0})")
    (apply-macete-with-minor-premises tr%equinumerous-is-symmetric)
    (apply-macete-with-minor-premises rev%omega-1-is-singleton)
    (antecedent-inference-strategy (0))
    (instantiate-existential ("f"))
    insistent-direct-inference-strategy
    (backchain-backwards "with(f:[ind_1,nn],ran{f}=omega(1))")
    extensionality
    direct-inference
    (cut-with-single-formula "#(x_0,nn) or not(#(x_0,nn))")
    (antecedent-inference "with(x_0:zz,#(x_0,nn) or not(#(x_0,nn)))")
    simplify
    simplify
    direct-inference
    (contrapose "with(x_0:zz,not(#(x_0,nn)))")
    simplify
    )))


(def-theorem SINGLETON-HAS-F-CARD-ONE-LEMMA-2
  "forall(a:sets[ind_1], forsome(y:ind_1, a=singleton{y}) implies f_card{a}=1)"
  lemma
  (theory generic-theory-1)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (backchain "with(y:ind_1,a:sets[ind_1],a=singleton{y})")
    (weaken (0))
    (apply-macete-with-minor-premises iota-free-definition-of-f-card)
    direct-inference
    (instantiate-existential ("lambda(x:ind_1,if(x=y,0,?nn))"))
    extensionality
    direct-inference
    simplify
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-inference
    insistent-direct-inference
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    beta-reduce-insistently
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(m,n:nn, m=n)")
    (raise-conditional (0))
    simplify
    insistent-direct-inference
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    beta-reduce-insistently
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, not(p))")
    (instantiate-existential ("y"))
    simplify
    (weaken (0))
    insistent-direct-inference
    beta-reduce-insistently
    simplify
    sort-definedness
    beta-reduce-repeatedly
    simplify
    )))

(def-theorem SINGLETON-HAS-F-CARD-ONE
  "forall(a:sets[ind_1], f_card{a}=1 iff forsome(y:ind_1, a=singleton{y}))"
  reverse
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    direct-inference
    (apply-macete-with-minor-premises singleton-has-f-card-one-lemma-1)
    (apply-macete-with-minor-premises singleton-has-f-card-one-lemma-2)
    )))

(def-theorem SINGLETON-HAS-F-CARD-ONE-REWRITE 
  "forall(a:ind_1, f_card{singleton{a}}=1)"
  (theory generic-theory-1)
  (usages transportable-macete transportable-rewrite)
  (proof
   (
    (apply-macete-with-minor-premises tr%singleton-has-f-card-one)
    direct-inference
    (instantiate-existential ("a"))
    )))

(def-theorem POSITIVE-F-CARD-IFF-NONEMPTY
  "forall(a:sets[ind_1], 
     f_indic_q{a} implies 0<f_card{a} iff nonempty_indic_q{a})"
  reverse
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(a:sets[ind_1],0<f_card{a})")
    (cut-with-single-formula "a=empty_indic{ind_1}")
    (incorporate-antecedent "with(a:sets[ind_1],a=empty_indic{ind_1})")
    (apply-macete-with-minor-premises rev%empty-indic-has-f-card-zero)
    simplify
    (instantiate-transported-theorem equals-empty-indic-iff-empty () ("a"))
    (cut-with-single-formula "not(a=empty_indic{ind_1})")
    (instantiate-theorem empty-indic-has-f-card-zero ("a"))
    simplify
    extensionality
    (instantiate-existential ("x"))
    simplify
    )))


;;; SUBSET-OF-FINITE-INDIC-IS-FINITE lemma

(include-files
  (files (imps theories/cardinality/omega-embedding)))


(def-theorem subset-of-finite-cardinal-has-f-card
  "forall(a:sets[nn], n:nn,
     a subseteq omega(n) implies forsome(m:nn, m<=n and f_card{a}=m))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (apply-macete-locally rev%f-card-of-a-finite-cardinal (1) "m")
    (apply-macete-with-minor-premises 
     tr%f-card-equal-iff-finite-and-equinumerous)
    (apply-macete-with-minor-premises finite-cardinal-is-f-indic)
    (force-substitution 
     "((f_indic_q{a} or truth) and a equinumerous omega(m))"
     "a equinumerous omega(m)"
     (0))
    (apply-macete-with-minor-premises 
     subset-of-finite-cardinal-is-equinumerous)

    )))

(def-theorem set-embedding-in-finite-cardinal-has-f-card
  "forall(a:sets[ind_1], n:nn,
     a embeds omega(n) implies forsome(m:nn, m<=n and f_card{a}=m))"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (

    direct-inference
    direct-inference
    (cut-with-single-formula 
     "forsome(c:sets[nn], a equinumerous c and c subseteq omega(n))")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,forsome(c:sets[nn],p));")
     (antecedent-inference "with(p:prop,p and p);")
     (force-substitution "f_card{a}" "f_card{c}" (0))
     (apply-macete-with-minor-premises 
      subset-of-finite-cardinal-has-f-card)
     (apply-macete-with-minor-premises 
      tr%equinumerous-implies-f-card-quasi-equal))
    (apply-macete-with-minor-premises 
     tr%embeds-implies-equinumerous-to-subset)

    )))

(def-theorem subset-of-finite-indic-is-finite
  "forall(a,b:sets[ind_1],
     a subseteq b and f_indic_q{b} implies f_indic_q{a})"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (

    direct-inference
    (apply-macete-with-minor-premises iota-free-definition-of-f-indic-q)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "a embeds b")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (cut-with-single-formula "b equinumerous omega(n)")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (cut-with-single-formula "a embeds omega(n)")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (instantiate-theorem 
	set-embedding-in-finite-cardinal-has-f-card
	("a" "n"))
       (instantiate-existential ("m")))
      (instantiate-transported-theorem 
       embeds-equinumerous-transitivity
       ()
       ("a" "b" "omega(n)")))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises tr%f-card-equal-implies-equinumerous)
      (apply-macete-with-minor-premises f-card-of-a-finite-cardinal)))
    (apply-macete-with-minor-premises subset-embeds-in-superset)

    )))


;;; F-CARD vs. EMBEDS lemmas

(def-theorem NAT-NUMBER-LEQ-IFF-FINITE-CARDINAL-EMBEDS
  "forall(m,n:nn, m<=n iff omega(m) embeds omega(n))"
  reverse
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-inference
    direct-inference
    (instantiate-existential ("id{omega(m)}"))
    (apply-macete-with-minor-premises tr%dom-of-id)
    insistent-direct-inference
    beta-reduce-insistently
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (raise-conditional (0))
    (raise-conditional (0))
    simplify
    (apply-macete-with-minor-premises tr%id-is-injective-on-dom)
    (instantiate-transported-theorem 
     set-embedding-in-finite-cardinal-has-f-card 
     () 
     ("omega(m)" "n"))
    (incorporate-antecedent "with(m_$0,m:nn,f_card{omega(m)}=m_$0);")
    (apply-macete-with-minor-premises f-card-of-a-finite-cardinal)
    simplify
    )))

(def-theorem F-CARD-LEQ-IFF-FINITE-AND-EMBEDS
  "forall(a:sets[ind_1],b:sets[ind_2], 
     f_card{a} <= f_card{b} 
      iff 
     (f_indic_q{b} and (a embeds b)))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof				; 80 nodes
   (
    direct-inference
    direct-inference
    direct-inference
    (weaken (0))
    (cut-with-single-formula "f_indic_q{a} and f_indic_q{b}")
    (incorporate-antecedent "with(p,q:prop, p and q)")
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "f_card{a}=n_$0 and f_card{b}=n")
    (incorporate-antecedent "with(p,q:prop, p and q)")
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-card)
    direct-inference
    (antecedent-inference "with(p,q:prop, p and q)")
    (cut-with-single-formula "omega(n) equinumerous b")
    (cut-with-single-formula "a embeds omega(n)")
    (instantiate-transported-theorem 
     embeds-equinumerous-transitivity 
     () 
     ("a" "omega(n)" "b"))
    (cut-with-single-formula "omega(n_$0) embeds omega(n)")
    (instantiate-transported-theorem 
     equinumerous-embeds-transitivity 
     () 
     ("a" "omega(n_$0)" "omega(n)"))
    (apply-macete-with-minor-premises 
     rev%nat-number-leq-iff-finite-cardinal-embeds)
    simplify
    (apply-macete-with-minor-premises tr%equinumerous-is-symmetric)
    simplify
    simplify
    (antecedent-inference "with(p,q:prop, p and q)")
    (incorporate-antecedent "with(b:sets[ind_2],f_indic_q{b})")
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "f_card{b}=n and 0=0")
    (incorporate-antecedent "with(n:nn,b:sets[ind_2],f_card{b}=n)")
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-card)
    direct-inference
    (cut-with-single-formula "a embeds omega(n)")
    (cut-with-single-formula "forsome(m:nn, m<=n and f_card{a}=m)")
    (antecedent-inference "with(p:prop, forsome(m:nn,p))")
    (backchain-repeatedly 
     ("with(a:sets[ind_1],n,m:nn,m<=n and f_card{a}=m)" 
      "with(n:nn,b:sets[ind_2],f_card{b}=n and 0=0)"))
    (apply-macete-with-minor-premises 
     set-embedding-in-finite-cardinal-has-f-card)
    (instantiate-transported-theorem 
     embeds-equinumerous-transitivity 
     () 
     ("a" "b" "omega(n)"))
    )))


;;Added by jt Wed Jun 30 10:24:28 EDT 1993.

(def-theorem IMAGE-OF-A-FINITE-SET-IS-FINITE
  "forall(s:sets[ind_1],f:[ind_1,ind_2],
     f_indic_q{s} implies f_card{image{f,s}}<=f_card{s})"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (

    (apply-macete-with-minor-premises tr%f-card-leq-iff-finite-and-embeds)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forsome(phi:[ind_2,ind_1], forall(x:ind_2, 
       x in image{f_$1,s} implies phi(x) in s and f_$1 (phi(x))=x))")
    (move-to-sibling 1)
    choice-principle
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (case-split ("forsome(x:ind_1,x in s and x_$1=f_$1(x))"))
    (instantiate-existential ("x"))
    (instantiate-existential ("y_phi"))
    (instantiate-existential ("restrict{phi,image{f_$1,s}}"))
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "x_$2 in image{f_$1,s}")
    (incorporate-antecedent "with(x_$2:ind_2,f:sets[ind_2],x_$2 in f);")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    insistent-direct-inference
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x_$7"))
    (cut-with-single-formula "f_$1(phi(x_$1))=x_$1")
    (backchain "with(p:prop,f:sets[ind_2],
  forall(x:ind_2,x in f implies p and p));")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    insistent-direct-inference
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "x_$3 in image{f_$1,s}")
    (move-to-sibling 1)
    (contrapose "with(i,x_$5:ind_1,x_$5=i);")
    simplify
    (contrapose "with(i,x_$5:ind_1,x_$5=i);")
    simplify
    (contrapose "with(p:prop,not(p));")
    (backchain "with(i,x_$5:ind_1,x_$5=i);")
    (backchain "with(p:prop,forall(x:ind_2,p));")
    insistent-direct-inference
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "f_$1(phi(x_$1))=x_$1 and f_$1(phi(x_$2))=x_$2")
    simplify
    (backchain-backwards "with(p:prop,p and p);")
    (backchain "with(i:ind_1,i=i);")
    (backchain "with(p:prop,forall(x:ind_2,p));")
    (backchain "with(p:prop,forall(x:ind_2,p));")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (instantiate-existential ("x_$7"))
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (instantiate-existential ("x_$0"))

    )))

