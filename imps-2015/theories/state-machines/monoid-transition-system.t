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

(herald monoid-transition-system)
 
(load-section basic-monoids)

;;;(set (proof-log-port) (standard-output))

(include-files
   (files (imps theories/generic-theories/quotients)))

(def-constant prefix
  "lambda(m,n:uu, forsome(p:uu, n=m**p))"
  (theory monoid-theory))

(def-parse-syntax prefix
  (left-method infix-operator-method)
  (binding 150))

(def-print-syntax prefix
  (method present-binary-infix-operator)
  (token " prefix ")
  (binding 150))

(def-theorem prefix-is-transitive
  "forall(x,y,z:uu, x prefix y and y prefix z implies x prefix z)"
  (theory monoid-theory)
  (proof
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (backchain "with(p,y,z:uu,z=y**p);")
    (backchain "with(p_$0,x,y:uu,y=x**p_$0);")
    (instantiate-existential ("p_$0**p"))
    simplify
    )))

(def-theorem prefix-is-reflexive
  "forall(x:uu, x prefix x)"
  (theory monoid-theory)
  (proof
   (

   
    (unfold-single-defined-constant-globally prefix)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("e"))
    simplify

    )))

(def-constant init%eqv
  "lambda(a,b:uu, a=e and b=e or 
                  not a=e and not b=e and
                  forsome(x:uu, not x=e and x prefix a and x prefix b))"
   (theory monoid-theory))

(def-parse-syntax init%eqv
  (left-method infix-operator-method)
  (binding 150))

(def-print-syntax init%eqv
  (method present-binary-infix-operator)
  (token " init%eqv ")
  (binding 150))

(def-theory directed-monoid-theory
  (component-theories monoid-theory)
  (axioms
   (directed-property
    "forall(x,y,z:uu, 
       not x=e and not z=e and x prefix y and z prefix y 
         implies 
       forsome(u:uu, not u=e and u prefix x and u prefix z))")
   (no-units
    "forall(x:uu, x prefix e implies x=e)")
   ))  

(def-theorem init%eqv-reflexive-property
  "forall(x:uu, x init%eqv x)"
  (theory monoid-theory)
  (proof
   (


    (unfold-single-defined-constant-globally init%eqv)
    (unfold-single-defined-constant-globally prefix)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (instantiate-existential ("e"))
    simplify

    )))

(def-theorem init%eqv-symmetric-property
  "forall(x,y:uu,x init%eqv y iff y init%eqv x)"
  (theory monoid-theory)
  (proof
   (
    (unfold-single-defined-constant-globally init%eqv)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    auto-instantiate-existential
    )))

(def-theorem init%eqv-transitive-property
  "forall(x,y,z:uu, x init%eqv y and y init%eqv z implies  x init%eqv z)"
  (theory directed-monoid-theory)
  (proof
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(z:uu, not z=e and z prefix x_$1 and z prefix x_$0)")
    (move-to-sibling 1)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises directed-property)
      auto-instantiate-existential)
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(z:uu,p));")
      (instantiate-existential ("z_$0"))
      (block 
	(script-comment "`instantiate-existential' at (0 1)")
	(apply-macete-with-minor-premises prefix-is-transitive)
	(instantiate-existential ("x_$1")))
      (block 
	(script-comment "`instantiate-existential' at (0 2)")
	(apply-macete-with-minor-premises prefix-is-transitive)
	(instantiate-existential ("x_$0"))))

    )))

(def-translation generic-theory-to-directed-monoid
  (source generic-theory-1)
  (target directed-monoid-theory)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 uu))
  (theory-interpretation-check using-simplification))

(def-renamer gt-to-dm-renamer
  (pairs 
   (quotient quotient%uu) 
  )
  )

(def-transported-symbols quotient
  (translation generic-theory-to-directed-monoid)
  (renamer gt-to-dm-renamer)
  )  



(def-overloading quotient
  (generic-theory-1 quotient) (directed-monoid-theory quotient%uu))

(def-theorem ()
  "#(quotient(init%eqv))"
  (theory directed-monoid-theory)
  (proof
   (

    (unfold-single-defined-constant-globally quotient%uu)
    )))

(def-constant germ
  "quotient(init%eqv)"
  (theory  directed-monoid-theory))

(def-theorem totality-of-germ
  "forall(x:uu, #(germ(x)))"
  (theory  directed-monoid-theory)
  (usages d-r-convergence)
  (proof
   (
    insistent-direct-inference
    (unfold-single-defined-constant-globally germ)
    (unfold-single-defined-constant (0) quotient%uu)

    )))

(def-theorem germ-equality-condition
  "forall(m,n:uu, 
     germ(m)=germ(n) iff 
     (m=e and n=e or forsome(u:uu, not u=e and u prefix m and u prefix n)))"
  (theory directed-monoid-theory)
  (proof
   (


    (unfold-single-defined-constant-globally germ)
    (apply-macete-with-minor-premises tr%rev%quotient-map-for-equivalence-relations)
    (move-to-sibling 1)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      direct-and-antecedent-inference-strategy
      (apply-macete-with-minor-premises init%eqv-reflexive-property)
      (apply-macete-with-minor-premises init%eqv-symmetric-property)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (2 0 0 0 0)")
	(apply-macete-with-minor-premises init%eqv-transitive-property)
	(instantiate-existential ("y_$0"))))
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (unfold-single-defined-constant-globally init%eqv)
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0 1 1 0 0)")
	(contrapose "with(m,u:uu,u prefix m);")
	(backchain "with(m:uu,m=e);")
	(contrapose "with(u:uu,not(u=e));")
	(instantiate-theorem no-units ("u")))
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 1 0 1 0 0)")
	(contrapose "with(n,u:uu,u prefix n);")
	(backchain "with(n:uu,n=e);")
	(contrapose "with(u:uu,not(u=e));")
	(instantiate-theorem no-units ("u"))))

    )))

(def-theorem ()
  "nonempty_indic_q{ran{germ}}"
  (theory  directed-monoid-theory)
  (proof
   (

    (instantiate-existential ("germ(x)"))
    simplify-insistently
    (instantiate-existential ("x"))

    )))

(def-atomic-sort action
  "lambda(s:sets[uu], s in ran{germ})"
  (theory  directed-monoid-theory))

(def-language language-for-monoid-transition-system
  (embedded-languages monoid-theory)
  (base-types state)
  (constants
   (act "[state,uu,state ->  prop]")))

;Definition of the theory.

(def-theory monoid-transition-system
  (component-theories directed-monoid-theory)
  (language language-for-monoid-transition-system)
  (axioms
   (monoid-operation-behaves-as-composition
    "forall(s,t:uu, p,r:state,  
          act(p, s**t, r) iff 
          forsome(q:state, act(p,s,q) and act(q,t,r)))")
   (monoid-identity-behaves-as-identity
    "forall(p:state, act(p,e,p))")))

(define (PRESENT-TEX-STACK-LABEL formatter op args bp)
  (ignore bp)
  `(,(present-tree formatter (car args) 0)
    " \\stackrel\{"
    ,(present-tree formatter (cadr args) 0)
    "\}"
    "\{"
    ,(presentation-format formatter op)
    "\}"
    ,(present-tree formatter (caddr args) 0)))

(def-print-syntax act
  tex
  (token "\\rightarrow")
  (method present-tex-stack-label)
  (binding 150))

(def-constant accepted%transitions
  "lambda(p:state, indic{m:uu, forsome(q:state, act(p,m,q))})"
  (theory monoid-transition-system))

(def-constant refused%transitions
  "lambda(p:state, indic{m:uu, forall(q:state, not  act(p,m,q))})"
  (theory monoid-transition-system))

(def-theorem accepted%transitions-is-prefix-closed
  "forall(p:state, m,n:uu, m in accepted%transitions(p) and n prefix m implies n in accepted%transitions(p))"
  (theory monoid-transition-system)
  (proof
   (
    
    unfold-defined-constants
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (contrapose "with(q_$1:state,m:uu,p:state,act(p,m,q_$1));")
    (backchain "with(u,m:uu,m=u);")
    (apply-macete-with-minor-premises monoid-operation-behaves-as-composition)
    simplify
    )))

(def-constant accepted%actions
  "lambda(p:state, indic{a:action, 
                     forsome(m:uu,  germ(m)=a and m in accepted%transitions(p))})"
  (theory monoid-transition-system))

(def-constant refused%actions
  "lambda(p:state, 
      indic{a:action, forall(m:uu, germ(m)=a implies not m in accepted%transitions(p))})"
  (theory monoid-transition-system))

(def-theorem refused%actions-is-total
  "forall(p:state, #(refused%actions(p)))"
  (usages d-r-convergence)
  (theory monoid-transition-system)
  (proof
   (

    insistent-direct-inference
    (unfold-single-defined-constant-globally refused%actions)

    )))

(def-theorem accepted%actions-is-complement-of-refused%actions
  "forall(p:state, x:action, accepted%actions(p)^^=refused%actions(p))"
  lemma
  (theory monoid-transition-system)
  reverse
  (proof
   (


    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    unfold-defined-constants
    simplify-insistently

    )))

(def-constant failures
  "lambda(p:state, 
      lambda(u:uu, 
       indic{s:sets[action],
          forsome(q:state, act(p,u,q) and s subseteq refused%actions(q))}))"
  (theory monoid-transition-system))

(def-constant may%refuse%after
  "lambda(x:sets[action],u:uu,p:state,
      forsome(q:state,
        act(p,u,q) and x subseteq refused%actions(q)))"
  (theory monoid-transition-system))

(def-constant <_may%refuse
  "lambda(p,q:state, forall(x:sets[action],u:uu,  
        may%refuse%after(x,u,p) implies may%refuse%after(x,u,q)))"
  (theory monoid-transition-system))

(def-parse-syntax <_may%refuse
  (left-method infix-operator-method)
  (binding 150))

(def-print-syntax <_may%refuse
  (method present-binary-infix-operator)
  (token " <_may%refuse ")
  (binding 150))

(def-theorem failures-characterization-of-<_may%refuse
  "forall(p,q:state, p <_may%refuse q iff 
                     forall(u:uu, failures(p)(u) subseteq failures(q)(u)))"
  (theory  monoid-transition-system)
  (proof
   (


    unfold-defined-constants
    (unfold-single-defined-constant-globally may%refuse%after)
    simplify-insistently
    (prove-by-logic-and-simplification 0)

    )))


(def-constant must%refuse%after
  "lambda(x:sets[action],u:uu,p:state,
      forall(q:state,
        act(p,u,q) implies x subseteq refused%actions(q)))"
  (theory monoid-transition-system))


(def-theorem must%refuse%after-characterization-lemma
  "forall(x:sets[action],u:uu,p:state, 
	    must%refuse%after(x,u,p) iff 
            x subseteq big_i{lambda(q:state, if(act(p,u,q), refused%actions(q),sort_to_indic{action}))})"
  (theory  monoid-transition-system)
  lemma
  (proof
   (


    (unfold-single-defined-constant-globally must%refuse%after)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0)")
      (case-split ("act(p,u,i_$0)"))
      simplify
      simplify)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
      simplify-insistently
      insistent-direct-inference
      direct-and-antecedent-inference-strategy
      simplify
      (auto-instantiate-universal-antecedent
       "with(u:uu,p:state,x_$1:sets[action],
         forall(x_$0:action,
       	 x_$0 in x_$1
	 implies 
	 forall(i_$0:state,
	     x_$0 in if(act(p,u,i_$0),
      refused%actions(i_$0),
      sort_to_indic{action}))));")
      (instantiate-universal-antecedent "with(p:prop,forall(i_$0:state,p));"
					("q"))
      (simplify-antecedent "with(x_$0:action,f:sets[action],p:prop,x_$0 in if(p, f, f));"))


    )))

(def-constant successors%after
  "lambda(p:state, 
      lambda(u:uu, 
       indic{a:action,
          forsome(q:state, act(p,u,q) and a in accepted%actions(q))}))"
  (theory monoid-transition-system))

(def-theorem successors%after-complement
  "forall(p:state, u:uu,
	    big_i{lambda(q:state, 
			   if(act(p,u,q), refused%actions(q),sort_to_indic{action}))}=
	    successors%after(p)(u)^^)"
  (theory monoid-transition-system)
  (proof
   (


    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    (unfold-single-defined-constant-globally successors%after)
    simplify-insistently
    (apply-macete-with-minor-premises
     rev%accepted%actions-is-complement-of-refused%actions)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 0)")
      (instantiate-universal-antecedent "with(p:prop,forall(i_$0:state,p));"
                                         ("q"))
      (simplify-antecedent "with(x_$2:action,f:sets[action],x_$2 in f);"))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0 0 0)")
      (instantiate-universal-antecedent "with(p:prop,forall(q:state,p));"
                                         ("i_$1"))
      simplify
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	(case-split ("act(p,u,i_$1)"))
	simplify
	simplify))
    )))

(def-theorem must%refuse%after-characterization
  "forall(x:sets[action],u:uu,p:state, 
	    must%refuse%after(x,u,p) iff 
            x subseteq successors%after(p)(u)^^)"
  (theory  monoid-transition-system)
  (proof
   (


    (apply-macete-with-minor-premises must%refuse%after-characterization-lemma)
    (apply-macete-with-minor-premises successors%after-complement)

    )))

(def-constant <_must%refuse
  "lambda(p,q:state, forall(x:sets[action],u:uu,  
        must%refuse%after(x,u,p) implies must%refuse%after(x,u,q)))"
  (theory monoid-transition-system))

(def-parse-syntax <_must%refuse
  (left-method infix-operator-method)
  (binding 150))

(def-print-syntax <_must%refuse
  (method present-binary-infix-operator)
  (token " <_must%refuse ")
  (binding 150))

(def-theorem characterization-of-<_must%refuse
  "forall(p,q:state,
     q <_must%refuse p
      iff 
     forall(u:uu,successors%after(p)(u) subseteq successors%after(q)(u)));"
  (theory monoid-transition-system)
  (proof
   (


    (unfold-single-defined-constant-globally <_must%refuse)
    (apply-macete-with-minor-premises must%refuse%after-characterization)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
     (cut-with-single-formula "successors%after(q)(u)^^ subseteq successors%after(p)(u)^^")
     (move-to-sibling 1)
     (instantiate-universal-antecedent "with(p:prop,p);"
				       ("successors%after(q)(u)^^" "u"))
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (weaken (1))
      (incorporate-antecedent "with(p:prop,p);")
      simplify-insistently))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
     (cut-with-single-formula "successors%after(q)(u_$0)^^ subseteq successors%after(p)(u_$0)^^")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (weaken (2))
      (incorporate-antecedent "with(u_$0:uu,q:state,x_$1:sets[action],
  x_$1 subseteq successors%after(q)(u_$0)^^);")
      (incorporate-antecedent "with(p:prop,p);")
      simplify-insistently
      direct-and-antecedent-inference-strategy
      simplify)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (weaken (0))
      (incorporate-antecedent "with(p:prop,p);")
      simplify-insistently))

    )))
;%
;% In terms of testing based on the testing semantics of M. Hennessy

(def-constant must%accept%after
  "lambda(x:sets[action],u:uu,p:state,
     forall(q:state,
      act(p,u,q) implies not(x disj accepted%actions(q))))"
  (theory monoid-transition-system))

(def-constant may%accept%after
  "lambda(x:sets[action],u:uu,p:state,
     forsome(q:state,
      act(p,u,q) and not(x disj accepted%actions(q))))"
  (theory monoid-transition-system))

(def-theorem must%accept%after-negation-of-may%refuse%after
  "forall(p:state, x:sets[action],u:uu,  
       must%accept%after(x,u,p) iff not may%refuse%after(x,u,p))"
  (theory monoid-transition-system)    
  (proof
   (       


    unfold-defined-constants
    (apply-macete-with-minor-premises rev%accepted%actions-is-complement-of-refused%actions)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    simplify
    simplify                                                                     
    )))    

(def-theorem testing-characterization-of-<_may%refuse
  "forall(p,q:state, p <_may%refuse q iff 
                     forall(x:sets[action],u:uu,
                          must%accept%after(x,u,q) implies must%accept%after(x,u,p)))"
  (theory monoid-transition-system)
  (proof
   (


    (unfold-single-defined-constant-globally <_may%refuse)
    (apply-macete-with-minor-premises must%accept%after-negation-of-may%refuse%after)
    simplify
    direct-and-antecedent-inference-strategy
    simplify
    simplify

    )))


(def-theorem may%accept%after-negation-of-must%refuse%after
  "forall(p:state, x:sets[action],u:uu,  
       may%accept%after(x,u,p) iff not must%refuse%after(x,u,p))"
  (theory monoid-transition-system)    
  (proof
   (       


    unfold-defined-constants
    (apply-macete-with-minor-premises rev%accepted%actions-is-complement-of-refused%actions)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    simplify
    simplify                                                                     
    )))    


(def-theorem testing-characterization-of-<_must%refuse
  "forall(p,q:state, p <_must%refuse q iff 
                     forall(x:sets[action],u:uu,
                          may%accept%after(x,u,q) implies may%accept%after(x,u,p)))"
  (theory monoid-transition-system)
  (proof
   (


    (unfold-single-defined-constant-globally <_must%refuse)
    (apply-macete-with-minor-premises may%accept%after-negation-of-must%refuse%after)
    simplify
    direct-and-antecedent-inference-strategy
    simplify
    simplify

    )))

(def-theorem accepted%transitions-characterization-of-<_must%refuse
  "forall(p,q:state, 
      q <_must%refuse p 
           iff
      accepted%transitions(p) subseteq accepted%transitions(q))"
  (theory monoid-transition-system)
  (proof
   (


    (apply-macete-with-minor-premises characterization-of-<_must%refuse)
    (unfold-single-defined-constant-globally successors%after)
    (unfold-single-defined-constant-globally accepted%actions)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
      insistent-direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(u:uu,p));" ("x"))
      (incorporate-antecedent "with(x:uu,f:sets[uu],x in f);")
      (unfold-single-defined-constant-globally accepted%transitions)
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(x_$0:action,p));"
					("germ(e)"))
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	(instantiate-universal-antecedent "with(p:prop,forall(q_$3:state,p));"
					  ("q_$0"))
	(instantiate-universal-antecedent "with(p:prop,forall(m_$1:uu,p));"
					  ("e"))
	(simplify-antecedent "with(p:prop,not(p));")
	(block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	  (contrapose "with(p:prop,not(p));")
	  (unfold-single-defined-constant-globally accepted%transitions)
	  simplify-insistently
	  (instantiate-existential ("q_$0"))
	  (apply-macete-with-minor-premises monoid-identity-behaves-as-identity)))
      (instantiate-existential ("q_$2"))
      (block 
	(script-comment "`instantiate-universal-antecedent' at (1 1)")
	(apply-macete-with-minor-premises action-defining-axiom_directed-monoid-theory)
	simplify-insistently
	(instantiate-existential ("e"))))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0 0 0 0 0 0)")
      (incorporate-antecedent "with(f:sets[uu],f subseteq f);")
      (incorporate-antecedent "with(m_$0:uu,f:sets[uu],m_$0 in f);")
      (unfold-single-defined-constant-globally accepted%transitions)
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (instantiate-theorem monoid-operation-behaves-as-composition
			   ("u" "m_$0" "p" "q_$1"))
      (block 
	(script-comment "`instantiate-theorem' at (0 0 0 0)")
	(instantiate-universal-antecedent "with(p:prop,forall(x:uu,p));"
					  ("u**m_$0"))
	(instantiate-universal-antecedent "with(p:prop,forall(q_$0:state,p));"
					  ("q_$1"))
	(block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
	  (incorporate-antecedent "with(q_$3:state,m_$0,u:uu,q:state,act(q,u**m_$0,q_$3));")
	  (apply-macete-with-minor-premises monoid-operation-behaves-as-composition)
	  direct-and-antecedent-inference-strategy
	  (instantiate-existential ("q_$4"))
	  (instantiate-existential ("m_$0"))
	  (instantiate-existential ("q_$3"))))
      (instantiate-universal-antecedent "with(p:prop,forall(q:state,p));"
					("q_$0")))
    )))

;% Failures as independent objects

(def-constant support
  "lambda(f:[uu->sets[sets[action]]], indic{u:uu, nonempty_indic_q{f(u)}})"
  (theory directed-monoid-theory))

;% For a minor variant of this definition, see the file alternate-definitions
;% in this directory.

(def-constant failure_q
  "lambda(f:[uu, sets[sets[action]]], 
     forall(u:uu,x,y:sets[action], y in f(u) and x subseteq y implies x in f(u))
     and
     e in support(f)
     and
    forall(u,v:uu, u in support(f) and v prefix u implies v in support(f))
     and
    forall(u:uu, a:action, u in support(f) implies 
       (forsome(m:uu, germ(m)=a and (u**m) in support(f)) or
       forall(x:sets[action], x in f(u) implies  (x union singleton{a}) in f(u))))
     and
    total_q{f,[uu ->  sets[sets[action]]]}
     and
    forall(u:uu,s:sets[action], s in f(u) implies not (germ(e)) in s))"
  (theory directed-monoid-theory))

(def-theorem e-is-never-refused
  "forall(p:state, not(germ(e) in refused%actions(p)))"
  lemma
  (theory monoid-transition-system) 
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(x:action, germ(e) =x)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,p);")
     (backchain "with(p:prop,p);")
     (unfold-single-defined-constant-globally refused%actions)
     (unfold-single-defined-constant-globally accepted%transitions)
     (apply-macete-with-minor-premises indicator-facts-macete)
     beta-reduce-repeatedly
     (backchain-backwards "with(p:prop,p);")
     (weaken (0))
     simplify
     (instantiate-existential ("e"))
     (instantiate-existential ("p"))
     (apply-macete-with-minor-premises monoid-identity-behaves-as-identity))
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (instantiate-existential ("germ(e)"))
     (apply-macete-with-minor-premises action-defining-axiom_directed-monoid-theory)
     simplify-insistently
     (instantiate-existential ("e")))

    )))

(def-theorem range-of-failures
  "forall(p:state, failure_q(failures(p)))"
  (theory monoid-transition-system)
  (proof
   (

    unfold-defined-constants
    (unfold-single-defined-constant-globally support)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 0 0 0)")
      auto-instantiate-existential (apply-macete-with-minor-premises tr%subseteq-transitivity)
      auto-instantiate-existential
      )
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0)")
      (instantiate-universal-antecedent "with(p:prop,p);" ("p"))
      (instantiate-universal-antecedent "with(p:prop,p);" ("e" "empty_indic{action}"))
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	(contrapose "with(p:prop,p);") (instantiate-existential ("empty_indic{action}"))
	(instantiate-existential ("p"))
	(apply-macete-with-minor-premises monoid-identity-behaves-as-identity)
	simplify-insistently
	)
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0)")
	(instantiate-existential ("empty_indic{action}")) (instantiate-existential ("p"))
	(apply-macete-with-minor-premises monoid-identity-behaves-as-identity)
	simplify-insistently
	) )
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (2 0 0 0 0 0 0 0 0)")
      (instantiate-existential ("empty_indic{action}"))
      (incorporate-antecedent "with(u_$0,v_$0:uu,v_$0 prefix u_$0);")
      (unfold-single-defined-constant (0) prefix) direct-and-antecedent-inference-strategy
      (incorporate-antecedent "with(q_$0:state,u_$0:uu,p:state,act(p,u_$0,q_$0));")
      (backchain "with(u,u_$0:uu,u_$0=u);")
      (apply-macete-with-minor-premises monoid-operation-behaves-as-composition)
      direct-and-antecedent-inference-strategy (instantiate-existential ("q"))
      simplify-insistently
      )
    (block
      (script-comment "`direct-and-antecedent-inference-strategy' at (3 0 0 0 0 0 0 0 0 0 0 0 0)")
      auto-instantiate-existential (antecedent-inference "with(p:prop,p or p);") simplify
      (block 
	(script-comment "`antecedent-inference' at (1)")
	(cut-with-single-formula "forsome(m:uu, germ(m)=a_$0)") (move-to-sibling 1)
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (cut-with-single-formula "#(a_$0, action)")
	  (incorporate-antecedent "with(a_$0:action,#(a_$0,action));")
	  (apply-macete-with-minor-premises action-defining-axiom_directed-monoid-theory)
	  simplify-insistently direct-and-antecedent-inference-strategy
	  (instantiate-existential ("x_$0"))
	  )
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (antecedent-inference "with(p:prop,forsome(m:uu,p));")
	  (unfold-single-defined-constant-globally refused%actions) simplify-insistently
	  (backchain "with(a_$0,x:action,x=a_$0);")
	  (backchain-backwards "with(a_$0:action,m:uu,germ(m)=a_$0);")
	  (apply-macete-with-minor-premises germ-equality-condition)
	  direct-and-antecedent-inference-strategy
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
	    (instantiate-universal-antecedent "with(p:prop,forall(m_$0:uu,p));" ("m"))
	    (instantiate-universal-antecedent "with(p:prop,forall(x_$5:sets[action],p));" ("x_$5")
					      )
	    (instantiate-universal-antecedent "with(p:prop,forall(q_$0:state,p or p));" ("q_$0"))
	    (contrapose "with(p:prop,not(p));") simplify
	    )
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0)")
	    (instantiate-universal-antecedent "with(p:prop,forall(m_$0:uu,p));" ("u"))
	    (block 
	      (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	      (contrapose "with(a_$0:action,f:sets[uu],not(f=a_$0));")
	      (backchain-backwards "with(a_$0:action,m:uu,germ(m)=a_$0);")
	      (apply-macete-with-minor-premises germ-equality-condition)
	      direct-and-antecedent-inference-strategy
	      (block 
		(script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
		(instantiate-existential ("u"))
		(apply-macete-with-minor-premises prefix-is-reflexive)
		)
	      (instantiate-existential ("u"))
	      )
	    (block 
	      (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	      (instantiate-universal-antecedent "with(p:prop,forall(x_$5:sets[action],p));"
						("empty_indic{action}")
						)
	      (contrapose "with(p:prop,forall(q_$0:state,p or p));")
	      (apply-macete-with-minor-premises monoid-operation-behaves-as-composition)
	      direct-and-antecedent-inference-strategy
	      (cut-with-single-formula "u in  accepted%transitions(q)") (move-to-sibling 1)
	      (block 
		(script-comment "`cut-with-single-formula' at (1)")
		(apply-macete-with-minor-premises accepted%transitions-is-prefix-closed)
		(instantiate-existential ("m_$0"))
		)
	      (block 
		(script-comment "`cut-with-single-formula' at (0)")
		(incorporate-antecedent "with(u:uu,q:state,u in accepted%transitions(q));")
		(unfold-single-defined-constant-globally accepted%transitions)
		simplify-insistently direct-and-antecedent-inference-strategy
		(instantiate-existential ("q_$1")) (instantiate-existential ("q"))
		) ) ) ) ) )
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (4 0 0 0 0 0 0)")
      (cut-with-single-formula "not(germ(e) in refused%actions(q))")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(contrapose "with(p:prop,not(p));") simplify
	)
      (apply-macete-with-minor-premises e-is-never-refused)
      )
    )))


(def-theorem not-everything-is-a-failure
  "not(failure_q(lambda(x:uu, empty_indic{sets[action]})))"
  (theory  directed-monoid-theory)
  lemma
  (proof
   (
    (unfold-single-defined-constant-globally failure_q)
    simplify-insistently
    (unfold-single-defined-constant-globally support)
    simplify-insistently
    )))

(def-constant stop_ff
  "lambda(x:uu, if(x=e, indic{s:sets[action], not (germ(e) in s)}, empty_indic{sets[action]}))"
  (theory  directed-monoid-theory))

(def-theorem stop-is-a-failure
  "failure_q(stop_ff)"
  (theory  directed-monoid-theory)
  (proof
   (


    unfold-defined-constants
    (unfold-single-defined-constant-globally support)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
      (case-split ("u_$0=e"))
      (block 
	(script-comment "`case-split' at (1)")
	(incorporate-antecedent "with(y_$0:sets[action],f:sets[sets[action]],y_$0 in f);")
	simplify
	direct-and-antecedent-inference-strategy
	(contrapose "with(p:prop,not(p));")
	simplify)
      (block 
	(script-comment "`case-split' at (2)")
	(incorporate-antecedent "with(y_$0:sets[action],f:sets[sets[action]],y_$0 in f);")
	simplify))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
      simplify
      (instantiate-existential ("empty_indic{action}"))
      simplify)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (2 0 0 0 0 0)")
      (cut-with-single-formula "v_$0=e")
      (move-to-sibling 1)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(instantiate-theorem no-units ("v_$0"))
	(contrapose "with(p:prop,not(p));")
	(cut-with-single-formula "u_$0=e")
	simplify
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (contrapose "with(x_$1:sets[action],u_$0:uu,
  x_$1
   in if(u_$0=e,
        indic{s:sets[action],  not(germ(e) in s)},
        empty_indic{sets[action]}));")
	  simplify))
      simplify)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (3 0 0 0 0 0 0 0)")
      (cut-with-single-formula "u_$0=e")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	simplify
	(incorporate-antecedent "with(x_$8:sets[action],u_$0:uu,
  x_$8
   in if(u_$0=e,
        indic{s:sets[action],  not(germ(e) in s)},
        empty_indic{sets[action]}));")
	simplify
	(apply-macete-with-minor-premises tr%union-disjunction-conversion)
	(cut-with-single-formula "forsome(x:action, germ(e)=x)")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (antecedent-inference "with(p:prop,forsome(x:action,p));")
	  (backchain "with(x:action,f:sets[uu],f=x);")
	  (backchain "with(x:action,f:sets[uu],f=x);")
	  (apply-macete-with-minor-premises tr%union-disjunction-conversion)
	  simplify
	  direct-and-antecedent-inference-strategy
	  (backchain-backwards "with(x:action,f:sets[uu],f=x);")
	  (weaken (1))
	  (instantiate-universal-antecedent "with(p:prop,forall(m_$0:uu,p));"
					    ("e"))
	  (contrapose "with(f:sets[sets[action]],empty_indic_q{f});")
	  (apply-macete-with-minor-premises right-multiplicative-identity-for-monoids)
	  simplify
	  (instantiate-existential ("empty_indic{action}"))
	  simplify)
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (instantiate-existential ("germ(e)"))
	  (apply-macete-with-minor-premises action-defining-axiom_directed-monoid-theory)
	  simplify
	  (instantiate-existential ("e"))))
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(contrapose "with(x_$1:sets[action],u_$0:uu,
  x_$1
   in if(u_$0=e,
        indic{s:sets[action],  not(germ(e) in s)},
        empty_indic{sets[action]}));")
	simplify))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (4 0)")
      insistent-direct-inference
      beta-reduce-repeatedly)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (5 0 0 0)")
      (cut-with-single-formula "u_$0=e")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(incorporate-antecedent "with(s_$0:sets[action],u_$0:uu,
  s_$0
   in if(u_$0=e,
        indic{s:sets[action],  not(germ(e) in s)},
        empty_indic{sets[action]}));")
	simplify)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(contrapose "with(s_$0:sets[action],u_$0:uu,
  s_$0
   in if(u_$0=e,
        indic{s:sets[action],  not(germ(e) in s)},
        empty_indic{sets[action]}));")
	simplify))


    )))

(def-atomic-sort ff
  "failure_q"
  (witness "stop_ff")
  (theory directed-monoid-theory))

;% Graded monoids for Timed CSP

(def-language language-for-graded-monoid
  (embedded-language directed-monoid-theory)
  (constants
   (lngth "[uu,rr]")))


(def-theory graded-monoid
  (language language-for-graded-monoid)
  (component-theories directed-monoid-theory)
  (axioms
   (divisibility 
    "forall(a:uu, not a=e implies 
                  forsome(b:uu, not b=e and b prefix a and 0<=lngth(b) and lngth(b)<=1))")
   (length-non-negative "forall(a:uu, 0<=lngth(a))")
   (length-of-product "forall(a,b:uu, lngth(a**b)=lngth(a)+lngth(b))")))

(def-theorem ()
  "forall(a:uu, #(lngth(a)))"
  (theory graded-monoid)
  (usages d-r-convergence)
  (proof
   (

    insistent-direct-inference
    (assume-theorem length-of-product)
    )))


(def-theorem lngth-of-e
  "lngth(e)=0"
  (theory graded-monoid)
  (proof
   (


    (cut-with-single-formula "lngth(e**e)=lngth(e)+lngth(e)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(p:prop,p);")
      simplify)
    (apply-macete-with-minor-premises length-of-product)
    )))

(def-theorem action-representatives-can-have-norm-le-1
  "forall(a:action, 
     forsome(u:uu, germ(u)=a and 0<=lngth(u) and lngth(u)<=1))"
  (theory graded-monoid)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(a,action)")
    (incorporate-antecedent "with(p:prop,p);")
    (apply-macete-with-minor-premises action-defining-axiom_directed-monoid-theory)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (case-split ("x=e"))
    (block 
     (script-comment "`case-split' at (1)")
     (instantiate-existential ("e"))
     simplify
     (block 
      (script-comment "`instantiate-existential' at (0 2)")
      (apply-macete-with-minor-premises lngth-of-e)
      simplify))
    (block 
     (script-comment "`case-split' at (2)")
     (instantiate-theorem divisibility ("x"))
     (instantiate-existential ("b"))
     (backchain "with(f:sets[uu],a:action,a=f);")
     (apply-macete-with-minor-premises germ-equality-condition)
     direct-and-antecedent-inference-strategy
     (instantiate-existential ("b"))
     (apply-macete-with-minor-premises prefix-is-reflexive))    )))

(def-theory graded-monoid-transition-system
  (component-theories graded-monoid monoid-transition-system))

(def-constant eqv%may%refuse
  "lambda(p,q:state, n:zz, forall(x:sets[action],u:uu,  lngth(u)<=n implies
        may%refuse%after(x,u,p) iff may%refuse%after(x,u,q)))"
  (theory graded-monoid-transition-system))

(def-theorem failures-characterization-of-eqv%may%refuse
  "forall(p,q:state, n:zz, eqv%may%refuse(p,q,n) iff 
                     forall(u:uu, lngth(u)<=n implies failures(p)(u)= failures(q)(u)))"
  (theory  graded-monoid-transition-system)
  (proof
   (

    unfold-defined-constants
    (unfold-single-defined-constant-globally may%refuse%after)
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify-insistently
    (prove-by-logic-and-simplification 0)

    )))

;To complete this circle of ideas, we introduce a relation
;on the sort STATE and prove p -> failures(p) separates precisely
;those pairs of points which are inequivalent

(def-parse-syntax =_may%refuse
  (left-method infix-operator-method)
  (binding 150))

(def-print-syntax =_may%refuse
  (method present-binary-infix-operator)
  (token " =_may%refuse ")
  (binding 150))


(def-constant =_may%refuse
  "lambda(p,q:state, forall(x:sets[action],u:uu,  
        may%refuse%after(x,u,p) iff may%refuse%after(x,u,q)))"
  (theory monoid-transition-system))


(def-theorem failures-characterization-of-=%may%refuse
  "forall(p,q:state, p =_may%refuse q iff failures(p)=failures(q))"
  (theory  graded-monoid-transition-system)
  (proof
   (

    (unfold-single-defined-constant (0) =_may%refuse)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
     extensionality
     (block 
      (script-comment "`extensionality' at (0)")
      direct-and-antecedent-inference-strategy
      (cut-with-single-formula "forall(p:state, x:uu, #(failures(p)(x)))")
      (move-to-sibling 1)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       direct-and-antecedent-inference-strategy
       (unfold-single-defined-constant (0) failures))
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       simplify
       (instantiate-universal-antecedent-multiply 
	"with(p:prop,forall(p:state,x:uu,with(p:prop,p)));"
	(("p" "x_0") ("q" "x_0")))
       simplify
       (cut-with-single-formula "eqv%may%refuse(p,q,1+floor(lngth(x_0)))")
       (move-to-sibling 1)
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(unfold-single-defined-constant (0) eqv%may%refuse)
	direct-and-antecedent-inference-strategy
	(backchain-backwards "with(p:prop,forall(x:sets[action],u:uu,p));")
	(backchain "with(p:prop,forall(x:sets[action],u:uu,p));"))
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(incorporate-antecedent "with(r:rr,q,p:state,eqv%may%refuse(p,q,r));")
	(apply-macete-with-minor-premises failures-characterization-of-eqv%may%refuse)
	direct-and-antecedent-inference-strategy
	simplify)))
     (unfold-single-defined-constant (0) failures)
     (unfold-single-defined-constant (0) failures))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
     (instantiate-theorem failures-characterization-of-eqv%may%refuse
			  ("p" "q" "1+floor(lngth(u))"))
     (block 
      (script-comment "`instantiate-theorem' at (0 0)")
      (incorporate-antecedent "with(r:rr,q,p:state,eqv%may%refuse(p,q,r));")
      (unfold-single-defined-constant (0) eqv%may%refuse)
      direct-and-antecedent-inference-strategy
      (backchain-backwards "with(p:prop,forall(x_$0:sets[action],u_$0:uu,p));")
      simplify)
     (block 
      (script-comment "`instantiate-theorem' at (0 1 0 0)")
      (contrapose "with(f:sets[sets[action]],not(f=f));")
      (cut-with-single-formula "forall(p:state, x:uu, #(failures(p)(x)))")
      (move-to-sibling 1)
      (unfold-single-defined-constant (0) failures)
      simplify))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 1)")
     (instantiate-theorem failures-characterization-of-eqv%may%refuse
			  ("p" "q" "1+floor(lngth(u))"))
     (block 
      (script-comment "`instantiate-theorem' at (0 0)")
      (incorporate-antecedent "with(r:rr,q,p:state,eqv%may%refuse(p,q,r));")
      (unfold-single-defined-constant (0) eqv%may%refuse)
      direct-and-antecedent-inference-strategy
      (backchain "with(p:prop,forall(x_$0:sets[action],u_$0:uu,p));")
      simplify)
     (block 
      (script-comment "`instantiate-theorem' at (0 1 0 0)")
      (contrapose "with(f:sets[sets[action]],not(f=f));")
      (cut-with-single-formula "forall(p:state, x:uu, #(failures(p)(x)))")
      (move-to-sibling 1)
      (unfold-single-defined-constant (0) failures)
      simplify))

    )))


