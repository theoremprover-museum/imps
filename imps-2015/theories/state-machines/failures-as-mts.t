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
;% COPYRIGHT NOTICE INSERTED: Fri Sep  2 14:41:02 EDT 1994

(herald failures-as-transition-system)

(include-files
   (files (imps theories/state-machines/monoid-transition-system)))

(def-constant act_ff
  "lambda(p:ff, a:uu, q:ff, forall(u:uu, q(u) subseteq p(a**u)))"
  (theory directed-monoid-theory))

(def-theorem act_ff-is-act
  "forall(s,t:uu,p,r:ff,
  act_ff(p,s**t,r)
   iff 
  forsome(q:ff,act_ff(p,s,q) and act_ff(q,t,r)))"
  (theory  directed-monoid-theory)
  (proof
   (

    (unfold-single-defined-constant-globally act_ff)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
      (instantiate-existential ("lambda(u:uu, p(s**u))"))
      beta-reduce-repeatedly
      (block 
	(script-comment "`instantiate-existential' at (0 1 0)")
	beta-reduce-repeatedly
	(incorporate-antecedent "with(t,s:uu,p,r:ff,forall(u:uu,r(u) subseteq p((s**t)**u)));")
	(apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids)
	simplify)
      (block 
	(script-comment "`instantiate-existential' at (1)")
	(cut-with-single-formula "#(p,ff)")
	(incorporate-antecedent "with(p:ff,#(p,ff));")
	(apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory)
	(unfold-single-defined-constant-globally failure_q)
	(unfold-single-defined-constant-globally support)
	(apply-macete-with-minor-premises indicator-facts-macete)
	beta-reduce-repeatedly
	direct-and-antecedent-inference-strategy
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 0 0)")
	  (backchain "with(p:prop,forall(u:uu,x,y:sets[action],p));")
	  (instantiate-existential ("y_$0")))
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
	  (backchain "with(p:prop,forall(u,v:uu,p));")
	  (instantiate-existential ("s**t"))
	  (block 
	    (script-comment "`instantiate-existential' at (0 0)")
	    (instantiate-universal-antecedent "with(f:sets[sets[action]],forall(u:uu,f subseteq f));"
					      ("e"))
	    (cut-with-single-formula "#(r,ff)")
	    (incorporate-antecedent "with(r:ff,#(r,ff));")
	    (apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory)
	    (unfold-single-defined-constant-globally failure_q)
	    direct-and-antecedent-inference-strategy
	    (incorporate-antecedent "with(f:sets[uu],e in f);")
	    (unfold-single-defined-constant-globally support)
	    simplify
	    direct-and-antecedent-inference-strategy
	    (instantiate-universal-antecedent "with(f:sets[sets[action]],f subseteq f);"
					      ("x_$0"))
	    (instantiate-existential ("x_$0"))
	    (simplify-antecedent "with(x_$0:sets[action],u:uu,p:ff,x_$0 in p(u**e));"))
	  (block 
	    (script-comment "`instantiate-existential' at (0 1)")
	    (unfold-single-defined-constant (0) prefix)
	    simplify
	    (instantiate-existential ("t"))))
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0 2 0 0 0 0 0 0 0)")
	  (backchain "with(p:prop,forall(u,v:uu,p));")
	  (instantiate-existential ("s**u_$0"))
	  (instantiate-existential ("x_$1"))
	  (block 
	    (script-comment "`instantiate-existential' at (0 1)")
	    (unfold-single-defined-constant (0) prefix)
	    (incorporate-antecedent "with(u_$0,v_$0:uu,v_$0 prefix u_$0);")
	    (unfold-single-defined-constant (0) prefix)
	    direct-and-antecedent-inference-strategy
	    (backchain "with(u,u_$0:uu,u_$0=u);")
	    (apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids)
	    (instantiate-existential ("p_$0"))))
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0 3 0 0 0 0 0 0 0 0
0)")
	  (instantiate-universal-antecedent "with(p:prop,forall(u:uu,a:action,p));"
					    ("s**u_$0" "a_$0"))
	  (instantiate-universal-antecedent "with(f:sets[sets[action]],empty_indic_q{f});"
					    ("x_$8"))
	  (block 
	    (script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0 0 0)")
	    (instantiate-universal-antecedent "with(p:prop,forall(m_$0:uu,p or p));"
					      ("m"))
	    (contrapose "with(f:sets[sets[action]],empty_indic_q{f});")
	    (instantiate-existential ("x_$2"))
	    (apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids))
	  (backchain "with(p:prop,forall(x:sets[action],p));"))
	simplify-insistently
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0 5 0 0 0 0 0)")
	  (apply-macete-with-minor-premises tr%subseteq-transitivity)
	  (backchain "with(p:prop,forall(u:uu,s:sets[action],p));")
	  auto-instantiate-existential)))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0 0)")
      (apply-macete-with-minor-premises tr%subseteq-transitivity)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
	(instantiate-existential ("q(t**u)"))
	simplify
	(block 
	  (script-comment "`instantiate-existential' at (0 1)")
	  (force-substitution "(s**t)**u" "s**(t**u)" (0))
	  simplify
	  (apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids))
	(block 
	  (script-comment "`instantiate-existential' at (1 0)")
	  (cut-with-single-formula "#(q,ff)")
	  (incorporate-antecedent "with(q:ff,#(q,ff));")
	  (apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory)
	  (unfold-single-defined-constant-globally failure_q)
	  direct-and-antecedent-inference-strategy))
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (1)")
	(cut-with-single-formula "#(p,ff)")
	(incorporate-antecedent "with(p:ff,#(p,ff));")
	(apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory)
	(unfold-single-defined-constant-globally failure_q)
	direct-and-antecedent-inference-strategy)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (2)")
	(cut-with-single-formula "#(r,ff)")
	(incorporate-antecedent "with(r:ff,#(r,ff));")
	(apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory)
	(unfold-single-defined-constant-globally failure_q)
	direct-and-antecedent-inference-strategy))
    )))

(def-theorem e-behaves-as-identity
  "forall(p:ff,act_ff(p,e,p))"
  (theory directed-monoid-theory)
  (proof
   (

    (unfold-single-defined-constant-globally act_ff)
    simplify
    )))



(def-translation monoid-transition-system-to-directed-monoid-theory
  (source monoid-transition-system)
  (target directed-monoid-theory)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (state ff)) 
  (constant-pairs (act act_ff))
  (theory-interpretation-check using-simplification))

(def-renamer mts-to-dmt
  (pairs
   (failures failures_ff)
   (refused%actions refused%actions_ff)
   (accepted%transitions accepted%transitions_ff)
   (may%refuse%after may%refuse%after_ff)
   (<_may%refuse <_may%refuse_ff)))

;Let us not overload these for now to keep the differences clear:

(def-parse-syntax <_may%refuse_ff
  (left-method infix-operator-method)
  (binding 150))

(def-print-syntax <_may%refuse_ff
  (method present-binary-infix-operator)
  (token " <_may%refuse_ff ")
  (binding 150))

(def-transported-symbols
  (failures refused%actions accepted%transitions may%refuse%after <_may%refuse)
  (translation monoid-transition-system-to-directed-monoid-theory)
  (renamer  mts-to-dmt))

(def-constant transition
  "lambda(s:ff, r:uu, lambda(v:uu, s(r**v)))"
  (theory  directed-monoid-theory))

(def-theorem transition-maps-into-ff-condition
  "forall(s:ff, r:uu, #(transition(s,r),ff) iff r in support(s))"
  (theory   directed-monoid-theory)
  (proof
   (

    direct-inference
    (cut-with-single-formula "#(s,ff)")
    (incorporate-antecedent "with(p:prop,p);")
    (apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory)
    (unfold-single-defined-constant-globally transition)
    (unfold-single-defined-constant-globally failure_q)
    (unfold-single-defined-constant-globally support)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (simplify-antecedent "with(x:sets[action],r:uu,s:ff,x in s(r**e));")
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0 0 0 0 0 0)")
      (backchain "with(p:prop,forall(u_$0:uu,x_$8,y_$0:sets[action],p));")
      (instantiate-existential ("y_$0")))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 1 0 0 0)")
      (instantiate-existential ("x"))
      simplify)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 2 0 0 0 0 0 0 0
0)")
      (backchain "with(p:prop,forall(u_$0,v_$0:uu,p));")
      (instantiate-existential ("r**u_$0"))
      (instantiate-existential ("x"))
      (block 
	(script-comment "`instantiate-existential' at (0 1)")
	(unfold-single-defined-constant (0) prefix)
	(incorporate-antecedent "with(u_$0,v_$0:uu,v_$0 prefix u_$0);")
	(unfold-single-defined-constant (0) prefix)
	direct-and-antecedent-inference-strategy
	(backchain "with(u,u_$0:uu,u_$0=u);")
	(apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids)
	(instantiate-existential ("p"))))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 3 0 0 0 0 0 0 0
0 0 0)")
      (backchain "with(p:prop,forall(u_$0:uu,a_$0:action,p));")
      direct-and-antecedent-inference-strategy
      (instantiate-existential ("x"))
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0 0 0)")
	(instantiate-universal-antecedent "with(p:prop,forall(m_$0:uu,p or p));"
					  ("m_$0"))
	(incorporate-antecedent "with(f:sets[sets[action]],empty_indic_q{f});")
	(apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids)))
    simplify-insistently
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 5 0 0 0 0 0 0)")
      (backchain "with(p:prop,forall(u_$0:uu,s_$0:sets[action],p));")
      (instantiate-existential ("r**u_$0")))

    )))

(def-constant after_ff
  "lambda(p:ff, a:uu, iota(x:ff, x=transition(p,a)))"
  (theory  directed-monoid-theory))


(def-theorem iota-free-characterization-of-after_ff
  "forall(p,q:ff, a:uu, after_ff(p,a)=q iff (a in support(p) and transition(p,a)=q))"
  (theory  directed-monoid-theory)
  (proof
   (

    (unfold-single-defined-constant-globally after_ff)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      (contrapose "with(p:prop,p);")
      (apply-macete-with-minor-premises eliminate-iota-macete)
      (contrapose "with(p:prop,p);")
      (antecedent-inference-strategy (0))
      (cut-with-single-formula "#(transition(p,a),ff)")
      (incorporate-antecedent "with(f:[uu,sets[sets[action]]],#(f,ff));")
      (apply-macete-with-minor-premises transition-maps-into-ff-condition))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1)")
      (contrapose "with(q,f:ff,f=q);")
      (apply-macete-with-minor-premises eliminate-iota-macete)
      (contrapose "with(p:prop,not(p));"))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
      (apply-macete-with-minor-premises eliminate-iota-macete)
      direct-and-antecedent-inference-strategy)

    )))


(def-theorem factorization-of-act
  "forall(p,q:ff, a:uu, act_ff(p,a,q) iff
                        forall(u:uu, q(u) subseteq  transition(p,a)(u)))"
  (theory directed-monoid-theory)
  (proof
   (


    (unfold-single-defined-constant-globally act_ff)
    (unfold-single-defined-constant-globally transition)

    )))


(def-theorem accepted%transitions_ff-is-support
  "forall(s:ff, accepted%transitions_ff(s)=support(s))"
  (theory directed-monoid-theory)
  (proof
   (


    (unfold-single-defined-constant-globally accepted%transitions_ff)
    (unfold-single-defined-constant-globally act_ff)
    (unfold-single-defined-constant-globally support)
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0)")
      (instantiate-universal-antecedent "with(p:prop,p);" ("e"))
      (instantiate-existential ("x_$2"))
      (cut-with-single-formula "#(q,ff)")
      (incorporate-antecedent "with(q:ff,#(q,ff));")
      (apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory)
      (unfold-single-defined-constant-globally failure_q)
      direct-and-antecedent-inference-strategy
      (incorporate-antecedent "with(f:sets[uu],e in f);")
      (unfold-single-defined-constant-globally support)
      simplify
      direct-and-antecedent-inference-strategy
      (instantiate-existential ("x"))
      simplify
      (simplify-antecedent "with(f:sets[sets[action]],f subseteq f);")
      simplify)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0 0 0)")
      (instantiate-existential ("transition(s,x_$1)"))
      (unfold-single-defined-constant-globally transition)
      (block 
	(script-comment "`instantiate-existential' at (1)")
	(apply-macete-with-minor-premises transition-maps-into-ff-condition)
	(unfold-single-defined-constant-globally support)
	simplify
	(instantiate-existential ("x"))))
    )))


(comment (def-theorem failures_of_failures
  "forall(x:ff, failures_ff(x)=x)"
  (theory  directed-monoid-theory)
  (proof
   (


(unfold-single-defined-constant-globally failures_ff)
(unfold-single-defined-constant-globally refused%actions_ff)
(unfold-single-defined-constant-globally act_ff)
(apply-macete-with-minor-premises accepted%transitions_ff-is-support)
direct-and-antecedent-inference-strategy
extensionality
beta-reduce-repeatedly
simplify
(apply-macete-with-minor-premises tr%subseteq-antisymmetry)
simplify-insistently
direct-and-antecedent-inference-strategy

)))


 ("forall(x:ff, u:uu, failures_ff(x)(u) subseteq x(u))"


(unfold-single-defined-constant-globally failures_ff)
(unfold-single-defined-constant-globally refused%actions_ff)
(unfold-single-defined-constant-globally act_ff)
(apply-macete-with-minor-premises accepted%transitions_ff-is-support)
direct-and-antecedent-inference-strategy
(unfold-single-defined-constant-globally support)
insistent-direct-inference
direct-and-antecedent-inference-strategy
(apply-macete-with-minor-premises indicator-facts-macete)
beta-reduce-repeatedly
direct-and-antecedent-inference-strategy
(contrapose "with(p:prop,p);")
(incorporate-antecedent "with(p:prop,p);")
(apply-macete-with-minor-premises indicator-facts-macete)
beta-reduce-repeatedly
direct-and-antecedent-inference-strategy
(contrapose "with(p:prop,p);")
(force-substitution "forall(x_$1:action,
      x_$1 in x_$4
       implies 
      forall(m:uu,
        germ(m)=x_$1 implies empty_indic_q{q_$0(m)}))"
                    "forall(m:uu, germ(m) in x_$4 implies empty_indic_q{q_$0(m)})"
                    (0))
(move-to-sibling 1)
(block 
  (script-comment "`force-substitution' at (1)")
       direct-and-antecedent-inference-strategy
       simplify)

"forall(x:ff, u:uu, x(u) subseteq failures_ff(x)(u))"

(unfold-single-defined-constant-globally failures_ff)
(unfold-single-defined-constant-globally refused%actions_ff)
(unfold-single-defined-constant-globally act_ff)
(apply-macete-with-minor-premises accepted%transitions_ff-is-support)
direct-and-antecedent-inference-strategy
(unfold-single-defined-constant-globally support)
insistent-direct-inference
direct-and-antecedent-inference-strategy
(apply-macete-with-minor-premises indicator-facts-macete)
beta-reduce-repeatedly
direct-and-antecedent-inference-strategy
(contrapose "with(p:prop,p);")
(incorporate-antecedent "with(p:prop,p);")
(apply-macete-with-minor-premises indicator-facts-macete)
beta-reduce-repeatedly
direct-and-antecedent-inference-strategy
(contrapose "with(p:prop,p);")
(force-substitution "forall(x_$1:action,
      x_$1 in x_$4
       implies 
      forall(m:uu,
        germ(m)=x_$1 implies empty_indic_q{q_$0(m)}))"
                    "forall(m:uu, germ(m) in x_$4 implies empty_indic_q{q_$0(m)})"
                    (0))
(move-to-sibling 1)
(block 
 (script-comment "`force-substitution' at (1)")
       direct-and-antecedent-inference-strategy
       simplify)
(cut-with-single-formula "forall(x:ff, z:sets[action], z in x(e) implies forsome(q:ff, forall(u:uu,
q(u) subseteq x(u)) and forall(m:uu, germ(m) in z implies empty_indic_q{q(m)})))")
(instantiate-universal-antecedent "with(p:prop,forall(x:ff,z:sets[action],p));"
                                  ("after_ff(x_$3,u)" "x_$4"))
(contrapose "with(p:prop,not(p));")
(move-to-ancestor 4)
(block 
  (script-comment "`cut-with-single-formula' at (0)")
       (instantiate-universal-antecedent "with(p:prop,forall(x:ff,z:sets[action],p));"
                                         ("transition(x_$3,u)" "x_$4"))
       (block 
  (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
              (contrapose "with(p:prop,not(p));")
              (unfold-single-defined-constant (0) transition)
              (apply-macete-with-minor-premises right-multiplicative-identity-for-monoids))
       (block 
  (script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0)")
              (incorporate-antecedent "with(f:sets[sets[action]],forall(u_$0:uu,f subseteq f));")
              (unfold-single-defined-constant (0) transition)
              direct-and-antecedent-inference-strategy
              auto-instantiate-existential)
       (block 
  (script-comment "`instantiate-universal-antecedent' at (1 1)")
              (apply-macete-with-minor-premises transition-maps-into-ff-condition)
              (unfold-single-defined-constant (0) support)
              simplify-insistently
              auto-instantiate-existential))

))