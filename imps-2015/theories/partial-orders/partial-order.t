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


(herald partial-order)

(load-section foundation)


(def-language language-for-partial-order
  (base-types uu)
  (constants (prec "[uu,uu,prop]")))

(def-parse-syntax prec
  (left-method infix-operator-method)
  (binding 80))

(def-print-syntax prec
  (token " prec ")
  (method present-binary-infix-operator) 
  (binding 80))

(def-print-syntax prec
  tex
  (token " \\preceq ")
  (method present-tex-binary-infix-operator) 
  (binding 80))

(def-theory partial-order
  (language language-for-partial-order)
  (component-theories h-o-real-arithmetic)
  (axioms
   (prec-transitivity
    "forall(a,b,c:uu, a prec b and b prec c implies a prec c)")
   (prec-reflexivity
    "forall(a:uu, a prec a)")
   (prec-anti-symmetry
    "forall(a,b:uu, a prec b and b prec a implies a = b)")))

(def-constant rev%prec
  "lambda(a,b:uu, b prec a)"
  (theory partial-order)
  (usages rewrite))

(def-parse-syntax rev%prec
  (left-method infix-operator-method)
  (binding 80))

(def-print-syntax rev%prec
  (token " rev%prec ")
  (method present-binary-infix-operator) 
  (binding 80))

(def-theorem ()
  "forall(a,c:uu,
     forsome(b:uu,b prec a and c prec b) implies c prec a)"
  lemma
  (proof (direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises prec-transitivity)
	  auto-instantiate-existential))
  (theory partial-order))

(def-theorem ()
  "forall(a,b:uu,b prec a and a prec b implies a=b)"
  lemma
  (proof (direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises prec-anti-symmetry)
	  simplify))
  (theory partial-order))

(set (current-theory) (name->theory 'partial-order))

(def-theorem ()
  "prec = lambda(a,b:uu, a prec b)"
  lemma
  (proof (extensionality
	  direct-and-antecedent-inference-strategy
	  beta-reduce-repeatedly))
  (theory partial-order))


(def-constant prec%majorizes  
  "lambda(y:uu,s:sets[uu], forall(x:uu, x in s implies x prec y))"
  (theory partial-order))

(def-parse-syntax prec%majorizes
  (left-method infix-operator-method)
  (binding 75))

(def-print-syntax prec%majorizes
  (token " prec%majorizes ")
  (method present-binary-infix-operator) 
  (binding 75))

(def-print-syntax prec%majorizes
  tex
  (token " \\sqsupseteq ")
  (method present-tex-binary-infix-operator) 
  (binding 75))

(def-constant prec%sup
  "lambda(s:sets[uu],
        iota(y:uu, y prec%majorizes s and 
                   forall(z:uu, z prec%majorizes s implies y prec z)))"
  (theory partial-order))

(def-theorem iota-free-characterization-of-prec%sup
  "forall(s:sets[uu],y:uu,
      prec%sup(s)=y
       iff 
     (y prec%majorizes s
       and 
      forall(y_1:uu,y_1 prec%majorizes s implies y prec y_1)))"
  (theory partial-order)
  (usages transportable-macete)
  (proof
   (

    
    (unfold-single-defined-constant-globally prec%sup)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,p);")
    (eliminate-defined-iota-expression 0 w)
    (contrapose "with(p:prop,forall(w_1:uu,p));")
    (instantiate-existential ("w"))
    (contrapose "with(p:prop,not(p));")
    simplify
    (incorporate-antecedent "with(y,u:uu,u=y);")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises prec-anti-symmetry)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    )))

(def-theorem iota-free-characterization-of-prec%sup-existence
  "forall(s:sets[uu],y:uu,
      #(prec%sup(s))
       iff 
     forsome(y:uu,
             y prec%majorizes s
                  and 
             forall(y_1:uu,y_1 prec%majorizes s implies y prec y_1)))"

  (theory partial-order)
  (usages transportable-macete)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(v:uu, prec%sup(s)=v)")
    (move-to-sibling 1)
    (instantiate-existential ("prec%sup(s)"))
    (antecedent-inference "with(p:prop,forsome(v:uu,p));")
    (incorporate-antecedent "with(v,u:uu,u=v);")
    (apply-macete-with-minor-premises iota-free-characterization-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("v"))
    (cut-with-single-formula "forsome(v:uu, prec%sup(s)=v)")
    (antecedent-inference "with(p:prop,forsome(v:uu,p));")
    (apply-macete-with-minor-premises iota-free-characterization-of-prec%sup)
    auto-instantiate-existential

    )))



(def-theorem prec%majorizes-property-of-prec%sup
  "forall(s:sets[uu], #(prec%sup(s)) implies prec%sup(s) prec%majorizes s)"
  (theory partial-order)
  (usages transportable-macete)
  (proof 

   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(v:uu, prec%sup(s)=v)")
    (antecedent-inference "with(p:prop,forsome(v:uu,p));")
    (backchain "with(v,u:uu,u=v);")
    (incorporate-antecedent "with(v,u:uu,u=v);")
    (apply-macete-with-minor-premises iota-free-characterization-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("prec%sup(s)"))

    )))

(def-theorem lub-property-of-prec%sup
  "forall(s:sets[uu], y:uu, 
           y prec%majorizes s and #(prec%sup(s)) 
            implies
           prec%sup(s) prec y)"
  (theory partial-order)
  (usages transportable-macete)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(v:uu, prec%sup(s)=v)")
    (antecedent-inference "with(p:prop,forsome(v:uu,p));")
    (backchain "with(v,u:uu,u=v);")
    (incorporate-antecedent "with(v,u:uu,u=v);")
    (apply-macete-with-minor-premises iota-free-characterization-of-prec%sup)
    direct-and-antecedent-inference-strategy
    simplify
    (instantiate-existential ("prec%sup(s)"))
    )))

(def-theorem monotonicity-of-prec%sup
  "forall(s,t:sets[uu], s subseteq t and #(prec%sup(t)) and #(prec%sup(s))
                          implies
                        prec%sup(s) prec prec%sup(t))"
  (usages transportable-macete)
  (theory partial-order)
  (proof ((apply-macete-with-minor-premises lub-property-of-prec%sup)
	  direct-and-antecedent-inference-strategy
	  (unfold-single-defined-constant (0) prec%majorizes)
	  direct-and-antecedent-inference-strategy
	  (cut-with-single-formula "prec%sup(t) prec%majorizes t")
	  (incorporate-antecedent 0)
	  (unfold-single-defined-constant (0) prec%majorizes)
	  direct-and-antecedent-inference-strategy
	  (backchain 0)
	  (backchain  "s subseteq t")
	  (apply-macete-with-minor-premises prec%majorizes-property-of-prec%sup))))

(def-constant prec%increasing
  "lambda(s:[zz,uu],forall(n,p:zz,n<=p and #(s(n)) and #(s(p)) implies s(n) prec s(p)))"
  (theory partial-order))

(def-theory mappings-into-a-partial-order
  (component-theories partial-order generic-theory-1))

(def-translation index-on-zz
  force-under-quick-load
  (source mappings-into-a-partial-order)
  (target partial-order)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 zz)))

(def-theorem prec%majorizes%characterization
  "forall(x:uu, s:[ind_1,uu], x prec%majorizes ran{s} 
             iff 
          forall(n:ind_1, #(s(n)) implies s(n) prec x))"
  (proof (unfold-defined-constants
	  simplify-insistently
	  direct-and-antecedent-inference-strategy
	  (backchain 1)
	  (instantiate-existential ("n"))
	  (backchain 0)
	  (backchain 1)))
  (usages transportable-macete)
  (theory mappings-into-a-partial-order))

(def-translation order-reverse
  force-under-quick-load
  (source partial-order)
  (target partial-order)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs (prec rev%prec)
		  (rev%prec prec))
  (theory-interpretation-check using-simplification))

(def-renamer first-renamer
  (pairs
   (prec%majorizes prec%minorizes)
   (prec%increasing rev%prec%increasing)
   (prec%sup prec%inf)))

(def-transported-symbols (prec%increasing prec%majorizes prec%sup)
  (translation order-reverse)
  (renamer first-renamer))

(def-parse-syntax prec%minorizes
  (left-method infix-operator-method)
  (binding 75))

(def-print-syntax prec%minorizes
  (token " prec%minorizes ")
  (method present-binary-infix-operator) 
  (binding 75))

(def-print-syntax prec%minorizes
  tex
  (token " \\sqsubseteq ")
  (method present-tex-binary-infix-operator) 
  (binding 75))

(def-constant prec%lim%inf
  "lambda(s:[zz,uu], 
     prec%sup(ran(lambda(n:zz,prec%inf(ran{lambda(m:zz,if(n<=m,s(m),?uu))})))))"
  (theory partial-order))

(def-renamer second-renamer
  (pairs
   (prec%lim%inf prec%lim%sup)))

(def-transported-symbols (prec%lim%inf)
  (translation order-reverse)
  (renamer second-renamer))

(def-theorem minorizes-property-of-prec%sup
  "forall(s:sets[uu], y:uu, 
         forsome(z:uu, z in s and y prec z) and #(prec%sup(s)) 
                  implies 
                 y prec prec%sup(s))"
  (theory partial-order)
  (proof (direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises prec-transitivity)
	  auto-instantiate-existential
	  (cut-with-single-formula "prec%sup(s) prec%majorizes s")
	  (incorporate-antecedent 0)
	  (unfold-single-defined-constant (0) prec%majorizes)
	  direct-and-antecedent-inference-strategy
	  (backchain "forall(x:uu,x in s implies x prec prec%sup(s))")
	  (apply-macete-with-minor-premises prec%majorizes-property-of-prec%sup)))
  (usages transportable-macete))

(def-theorem prec%sup-dominates-values
  "forall(s:[ind_1,uu], x:ind_1, x in dom{s} and #(prec%sup(ran{s})) implies s(x) prec prec%sup(ran{s}))"
  (usages transportable-macete)

  (proof
   ((apply-macete-with-minor-premises minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("s(x)"))
    (apply-macete-with-minor-premises tr%range-domain-membership)
    (apply-macete-with-minor-premises prec-reflexivity)
    simplify
    (antecedent-inference 0)))

  (theory mappings-into-a-partial-order))

(def-theorem monotonicity-of-prec%sup-of-range
  "forall(f,g:[ind_1,uu], #(prec%sup(ran{f})) and #(prec%sup(ran{g})) and forall(x:ind_1, #(f(x)) implies f(x) prec g(x)) implies prec%sup(ran{f}) prec prec%sup(ran{g}))"

  (usages transportable-macete)

  (proof

   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises lub-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises prec%majorizes%characterization)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises prec-transitivity)
    (instantiate-existential ("g(n)"))
    (backchain "with(p:prop,   forall(x:ind_1,p))")
    (apply-macete-with-minor-premises prec%sup-dominates-values)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (cut-with-single-formula "f(n) prec g(n)")
    
    
    )

   )
  (theory mappings-into-a-partial-order))

(def-theory complete-partial-order
  (component-theories partial-order)
  (axioms
   (prec-completeness
    "forall(p:[uu,prop], nonvacuous_q{p} and forsome(alpha:uu, 
 forall(theta:uu,p(theta) implies theta prec alpha)) implies
forsome(gamma:uu,forall(theta:uu,p(theta) implies theta prec gamma) and forall(gamma_1:uu, 
 forall(theta:uu,p(theta) implies theta prec gamma_1) implies gamma prec gamma_1)))")))

(def-theorem prec%sup-defined
  "forall(s:sets[uu],nonempty_indic_q{s} and forsome(y:uu,y prec%majorizes s) 
                     implies
                    #(prec%sup(s)))"
  (theory complete-partial-order)
  (usages transportable-macete)
  (proof 

   (
    
    (apply-macete-with-minor-premises iota-free-characterization-of-prec%sup-existence)
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-theorem prec-completeness ("lambda(x:uu, x in s)"))
    (simplify-antecedent "with(s:sets[uu],
  forall(x_0:uu,not(lambda(x:uu,x in s)(x_0))));")
    (instantiate-universal-antecedent "with(s:sets[uu],empty_indic_q{s});" ("x"))
    (contrapose "with(p:prop,forall(alpha:uu,forsome(theta:uu,p)));")
    beta-reduce-repeatedly
    (instantiate-existential ("y"))
    (beta-reduce-antecedent "with(gamma:uu,s:sets[uu],
  forall(gamma_1:uu,
    forall(theta:uu,
      lambda(x:uu,x in s)(theta) implies theta prec gamma_1)
     implies 
    gamma prec gamma_1));")
    (instantiate-existential ("gamma"))
    (backchain "with(gamma:uu,f:[uu,prop],
  forall(theta:uu,f(theta) implies theta prec gamma));")
    simplify

    )))


(def-theorem complete-implies-bicomplete
  "forall(s:sets[uu],
     nonempty_indic_q{s} and forsome(y:uu,y prec%minorizes s)
      implies 
     #(prec%inf(s)))"
  (theory complete-partial-order)
  (proof
   (

    
    (apply-macete-with-minor-premises tr%iota-free-characterization-of-prec%sup-existence)
    unfold-defined-constants
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("prec%sup(indic{z:uu, z prec%minorizes s})"))
    (cut-with-single-formula "forsome(w:uu, prec%sup(indic{z:uu,  z prec%minorizes s})=w)")
    (antecedent-inference "with(p:prop,forsome(w:uu,p));")
    (backchain "with(w,u:uu,u=w);")
    (incorporate-antecedent "with(w,u:uu,u=w);")
    (apply-macete-with-minor-premises iota-free-characterization-of-prec%sup)
    unfold-defined-constants
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(w:uu,p:prop,
  forall(y_1:uu,
    forall(x_$0:uu,forall(x:uu,p) implies x_$0 prec y_1)
     implies 
    w prec y_1));")
    direct-and-antecedent-inference-strategy
    simplify
    (instantiate-existential ("prec%sup(indic{z:uu,  z prec%minorizes s})"))
    (move-to-sibling 1)
    (weaken (0))
    (block (script-comment "this part of the proof shows the prec%sup is defined.")
	   (apply-macete-with-minor-premises prec%sup-defined)
	   unfold-defined-constants
	   simplify-insistently
	   direct-and-antecedent-inference-strategy)
    (instantiate-existential ("y"))
    (instantiate-existential ("x"))
    simplify
    simplify-insistently
    (apply-macete-with-minor-premises minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    unfold-defined-constants
    simplify-insistently
    (instantiate-existential ("y_$0"))
    (apply-macete-with-minor-premises prec-reflexivity)
    

    )))

(def-theorem unfolded-completeness-from-below-condition
  "forall(p:[uu,prop],
     nonvacuous_q{p}
      and 
     forsome(alpha:uu,
       forall(theta:uu,p(theta) implies alpha prec theta))
      implies 
     forsome(gamma:uu,
       forall(theta:uu,p(theta) implies gamma prec theta)
        and 
       forall(gamma_1:uu,
         forall(theta:uu,p(theta) implies gamma_1 prec theta)
          implies 
         gamma_1 prec gamma)))"
  lemma
  (theory complete-partial-order)
  (usages transportable-macete)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (instantiate-theorem complete-implies-bicomplete ("indic{x:uu, p(x)}"))
    (contrapose "with(f:sets[uu],empty_indic_q{f});")
    simplify-insistently
    (instantiate-existential ("x_0"))
    (contrapose "with(p:prop,forall(y:uu,not(p)));")
    unfold-defined-constants
    unfold-defined-constants
    simplify-insistently
    (instantiate-existential ("alpha"))
    (incorporate-antecedent "with(u:uu,#(u));")
    (apply-macete-with-minor-premises tr%iota-free-characterization-of-prec%sup-existence)
    unfold-defined-constants
    unfold-defined-constants
    simplify-insistently

    )))


(def-translation complete-order-reverse
  force-under-quick-load
  (source complete-partial-order)
  (target complete-partial-order)
  (core-translation order-reverse)
  (theory-interpretation-check using-simplification))

(comment
 (def-theory-instance bi-complete-partial-order
  (source complete-partial-order)
  (target complete-partial-order)
  (translation order-reverse)
  (new-translation-name complete-order-reverse)))

;;;Not needed

;;;(def-theorem prec%minorizes-property-of-prec%inf
;;;  prec%majorizes-property-of-prec%sup
;;;  (theory bi-complete-partial-order)
;;;  (proof existing-theorem)
;;;  (usages transportable-macete)
;;;  (translation complete-order-reverse))
;;;
;;;;;;Not needed
;;;
;;;(def-theorem glb-property-of-prec%inf
;;;  lub-property-of-prec%sup
;;;  (theory bi-complete-partial-order)
;;;  (proof existing-theorem)
;;;  (usages transportable-macete)
;;;  (translation complete-order-reverse))
;;;
;;;;;;Not needed
;;;
;;;(def-theorem prec%inf-defined
;;;  prec%sup-defined
;;;  (theory bi-complete-partial-order)
;;;  (proof existing-theorem)
;;;  (usages transportable-macete)
;;;  (translation complete-order-reverse))



;;;(def-theorem monotonicity-of-prec%inf
;;;   monotonicity-of-prec%sup
;;;   (proof existing-theorem)
;;;   (translation  complete-order-reverse)
;;;   (usages transportable-macete)
;;;   (theory bi-complete-partial-order))
;;;


(def-theorem decreasing-property-of-sup-tail
  "forall(s:[zz,uu], 
   rev%prec%increasing(lambda(m:zz,prec%sup(ran{lambda(k:zz,if(m<=k,s(k),?uu))}))))"
  (theory partial-order)
  (proof
   (

    (unfold-single-defined-constant (0) rev%prec%increasing)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) rev%prec)
    (apply-macete-with-minor-premises monotonicity-of-prec%sup)
    direct-and-antecedent-inference-strategy
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x_$1"))
    simplify


    )))
;;;(def-theorem increasing-property-of-inf-tail
;;;  decreasing-property-of-sup-tail
;;;  (translation  complete-order-reverse)
;;;  (usages transportable-macete)
;;;  (proof existing-theorem)
;;;  (theory bi-complete-partial-order))


(def-theorem non-empty-range
  "forall(s:[ind_1,ind_2], nonempty_indic_q{ran{s}} iff forsome(x:ind_1, #(s(x))))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof (simplify-insistently
	  direct-and-antecedent-inference-strategy
	  (instantiate-existential ("x"))
	  (instantiate-existential ("s(x)"))
	  (instantiate-existential ("x")))))


;;;(def-theorem conditional-defined
;;;  "forall(x,y:ind_1, p:prop, x=if(p,y,?ind_1) iff (p and x=y))"
;;;  (proof ((raise-conditional (0))))
;;;  (theory generic-theory-1)
;;;  (usages transportable-macete))

(def-theorem ()
  "forall(a,b,c:uu,a rev%prec b and b rev%prec c implies a rev%prec c)"
  lemma  
  (proof (unfold-defined-constants
	  (apply-macete-with-minor-premises prec-transitivity)
	  direct-and-antecedent-inference-strategy
	  auto-instantiate-existential)) 
  (theory partial-order))

(def-theorem ()
  "prec=lambda(a,b:uu,b rev%prec a)"
  lemma
  (proof (unfold-defined-constants
	  extensionality
	  direct-and-antecedent-inference-strategy
	  beta-reduce-repeatedly))
  (theory partial-order))

(def-theorem ()
  "forall(a:uu,a rev%prec a)"
  lemma
  (proof (unfold-defined-constants
	  (apply-macete-with-minor-premises  prec-reflexivity)))
  (theory partial-order))


(def-theorem ()
  "forall(a,b:uu,a rev%prec b and b rev%prec a implies a=b)"
  lemma
  (proof (unfold-defined-constants
	  (apply-macete-with-minor-premises  prec-anti-symmetry)
	  direct-and-antecedent-inference-strategy))
  (theory partial-order))

(def-translation index-on-zz-reverse
  force-under-quick-load
  (source mappings-into-a-partial-order)
  (target partial-order)
  (core-translation order-reverse)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 zz)))
  
(def-theorem prec%lim%inf-existence
  "forall(s:[zz,uu], 
       forsome(n:zz,alpha,beta:uu,
              forall(p:zz,n<=p implies alpha prec s(p) and s(p) prec beta))
               implies 
          #(prec%lim%inf(s)))"


  (proof
   ((unfold-single-defined-constant (0) prec%lim%inf)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    beta-reduce-repeatedly
    (instantiate-existential ("n"))
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    beta-reduce-repeatedly
    (instantiate-existential ("n"))
    (instantiate-universal-antecedent 0 ("n"))
    (contrapose "with(n:zz,not(n<=n))")
    simplify
    simplify
    (instantiate-existential ("alpha"))
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) rev%prec)
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    (force-substitution
     "prec%inf(ran{lambda(m:zz,if(n_$0<=m, s(m), ?uu))}) prec y"
     "y rev%prec prec%inf(ran{lambda(m:zz,if(n_$0<=m, s(m), ?uu))})" (0))
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    (instantiate-existential ("beta"))
    (unfold-single-defined-constant (0) rev%prec)
    (cut-with-single-formula "forsome(k:zz,n_$0<=k and n<=k)")
    (instantiate-existential ("s(k)"))
    (force-substitution
     "s(k)"
     "lambda(m_$0:zz,if(n_$0<=m_$0, s(m_$0), ?uu))(k)" (0))
    (apply-macete-with-minor-premises tr%range-domain-membership)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (instantiate-universal-antecedent
     "with(beta:uu,s:[zz,uu],alpha:uu,n:zz,forall(p:zz,
                 n<=p implies alpha prec s(p) and s(p) prec beta))"
     ("k"))
    simplify
    simplify
    (backchain "with(beta:uu,s:[zz,uu],alpha:uu,n:zz,forall(p:zz,
                       n<=p implies alpha prec s(p) and s(p) prec beta))")
    simplify
    (instantiate-existential ("max(n_$0,n)"))
    (apply-macete-with-minor-premises maximum-1st-arg)
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (unfold-single-defined-constant (0) rev%prec)))
  (usages transportable-macete)
  
  (theory complete-partial-order))

(def-theorem prec%lim%inf-lower-bound
  "forall(s:[zz,uu],alpha:uu,
     #(prec%lim%inf(s))
      and 
     forsome(n:zz,forall(p:zz,n<=p implies alpha prec s(p)))
      implies 
     alpha prec prec%lim%inf(s))"
  (theory complete-partial-order)
  (usages transportable-macete)
  (proof
   (


    
    (unfold-single-defined-constant-globally prec%lim%inf)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential (" prec%inf(ran{lambda(m:zz,if(n<=m, s(m), ?uu))})"))
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-with-minor-premises
    (instantiate-existential ("n"))
    simplify
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    beta-reduce-repeatedly
    (instantiate-existential ("n"))
    (cut-with-single-formula "alpha prec s(n)")
    (move-to-sibling 1)
    simplify
    simplify
    (unfold-single-defined-constant (0) prec%minorizes)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) rev%prec)
    (instantiate-existential ("alpha"))
    (antecedent-inference "with(p:prop,forsome(x:zz,p));")
    (cut-with-single-formula "n<=x")
    (backchain "with(u,x_$1:uu,x_$1=u);")
    (weaken (1))
    simplify
    (contrapose "with(u,x_$1:uu,x_$1=u);")
    simplify
    (force-substitution "alpha prec prec%inf(ran{lambda(m:zz,if(n<=m, s(m), ?uu))})"
			" prec%inf(ran{lambda(m:zz,if(n<=m, s(m), ?uu))}) rev%prec alpha"
			(0))
    (move-to-sibling 1)
    (unfold-single-defined-constant (0) rev%prec)
    (apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) prec%minorizes)
    (unfold-single-defined-constant (0) rev%prec)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "n<=x")
    (backchain "with(u,x_$0:uu,x_$0=u);")
    (weaken (1))
    simplify
    (contrapose "with(u,x_$0:uu,x_$0=u);")
    simplify

    )))


(def-theorem prec%lim%inf-upper-bound
  "forall(s:[zz,uu],beta:uu,
     #(prec%lim%inf(s))
      and 
     forsome(n:zz,forall(p:zz,n<=p implies s(p) prec beta))
      implies 
     prec%lim%inf(s) prec beta)"
  
  (theory complete-partial-order)
  (usages transportable-macete)
  (proof
   (

    
    (unfold-single-defined-constant-globally prec%lim%inf)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises lub-property-of-prec%sup)
    (unfold-single-defined-constant (0) prec%majorizes)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (backchain "with(u,x_$0:uu,x_$0=u);")
    (force-substitution "prec%inf(ran{lambda(m_$0:zz,if(x_$4<=m_$0, s(m_$0), ?uu))}) prec beta"
			"beta rev%prec prec%inf(ran{lambda(m_$0:zz,if(x_$4<=m_$0, s(m_$0), ?uu))})"
			(0))
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) rev%prec)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (cut-with-single-formula "forsome(x:zz, x_$4<=x and n<=x)")
    (antecedent-inference "with(p:prop,forsome(x:zz,p));")
    (instantiate-existential ("s(x)"))
    (instantiate-existential ("x"))
    (cut-with-single-formula "s(x) prec beta")
    simplify
    simplify
    simplify
    simplify
    (instantiate-existential ("max(x_$4,n)"))
    (apply-macete-with-minor-premises maximum-1st-arg)
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (unfold-single-defined-constant (0) rev%prec)

    )))
