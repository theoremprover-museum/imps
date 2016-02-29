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


(herald relative-failures)

(load-section csp)

(def-theorem ptwise-closure-condition
  "forall(s:[zz,total%fns], aa:sets[sets[sets[action]]],
     #(lim(s)) and 
      forall(n:zz,u:uu, #(s(n)) implies s(n)(u) in aa )
        implies 
     forall(u:uu, lim(s)(u) in aa))"
  (theory graded-monoid)
  lemma
  (proof 
   (

 

    direct-inference
    direct-inference
    (cut-with-single-formula "forsome(x:total%fns, lim(s)=x)")
    (move-to-sibling 1)
    (instantiate-existential ("lim(s)"))
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     direct-and-antecedent-inference-strategy
     (backchain "with(p:prop,p and p);")
     (antecedent-inference "with(p:prop,forsome(x:total%fns,p));")
     (backchain "with(x,f:total%fns,f=x);")
     (incorporate-antecedent "with(x,f:total%fns,f=x);")
     (apply-macete-with-minor-premises characterization-ultrametric-limit-of-fns)
     direct-and-antecedent-inference-strategy
     (instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
				       ("1+floor(lngth(u))"))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
      (contrapose "with(p:prop,not(p));")
      (cut-with-single-formula "lngth(u)<=1+floor(lngth(u)) and 0<=lngth(u)")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises length-non-negative)
       simplify))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
      (backchain-backwards "with(p:prop,forall(p_$0:zz,u_$0:uu,p));")
      (instantiate-existential ("n_$0"))
      simplify
      simplify
      (block 
       (script-comment "`instantiate-existential' at (0 1)")
       (backchain "with(p:prop,f:total%fns,#(f) and forall(n:zz,u:uu,p));")
       (instantiate-universal-antecedent
	"with(p:prop,forall(p_$0:zz,u_$0:uu,p));"
	("n_$0" "u"))))))))


(def-constant rel%failure_q
  "lambda(f:[uu, sets[sets[action]]], aa:sets[sets[action]],  
        failure_q(f) and forall(u:uu, f(u) subseteq aa))"
  (theory  directed-monoid-theory))

(def-theorem rel%failure_q-is-closed-under-lim
  "forall(s:[zz,total%fns], aa:sets[sets[action]],
     #(lim(s)) and 
      forall(n:zz, #(s(n)) implies rel%failure_q(s(n),aa))
        implies 
      rel%failure_q(lim(s),aa))"
  (theory graded-monoid)
  (proof 
   (
     (let-script 
      prove-definedness 1
      ((cut-with-single-formula (% "#(~A,total%fns)" $1))
       (incorporate-antecedent "with(f:total%fns,#(f,total%fns));")
       (apply-macete-with-minor-premises total%fns-defining-axiom_graded-monoid)
       beta-reduce-with-minor-premises
       direct-and-antecedent-inference-strategy)
      )
     (unfold-single-defined-constant-globally rel%failure_q)
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment
       "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
      (apply-macete-with-minor-premises failure_q-is-closed-under-lim)
      direct-and-antecedent-inference-strategy
      (backchain "with(p:prop,forall(n:zz,p));"))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0)")
      (force-substitution "lim(s)(u) subseteq aa"
			  "lim(s)(u) in indic{b:sets[sets[action]], b subseteq aa}"
			  (0))
      (move-to-sibling 1)
      (block 
       (script-comment "`force-substitution' at (1)")
       (apply-macete-with-minor-premises indicator-facts-macete)
       beta-reduce-with-minor-premises
       ($prove-definedness "lim(s)"))
      (block 
       (script-comment "`force-substitution' at (0)")
       (apply-macete-with-minor-premises ptwise-closure-condition)
       direct-and-antecedent-inference-strategy
       (apply-macete-with-minor-premises indicator-facts-macete)
       beta-reduce-with-minor-premises
       (backchain "with(p:prop,forall(n:zz,p));")
       (block 
	(script-comment "`beta-reduce-with-minor-premises' at (1)")
	($prove-definedness "s(n)")))))

    ))

(def-constant rel%part
  "lambda(f:ff, aa:sets[sets[action]], lambda(u:uu, f(u) inters  aa))"
   (theory  directed-monoid-theory)) 

(def-theorem failure-non-empty-condition
  "forall(f:ff, u:uu, nonempty_indic_q{f(u)} iff empty_indic{action} in f(u))"
  (theory directed-monoid-theory)
  lemma
  reverse
  (proof
   (


    direct-inference
    (cut-with-single-formula "failure_q(f)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises ff-in-quasi-sort_directed-monoid-theory)
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (incorporate-antecedent "with(p:prop,p);")
     (unfold-single-defined-constant-globally failure_q)
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
      (backchain "with(p:prop,forall(u_$0:uu,x_$8,y_$0:sets[action],p));")
      auto-instantiate-existential
      simplify-insistently)
     auto-instantiate-existential)
    )))


(def-theorem rel%part-mapping-property
  "forall(aa:sets[sets[action]], 
     empty_indic{action} in aa and
     forall(x:action, a:sets[action], 
        a in aa implies a union singleton{x} in aa) and
     forall(b,a:sets[action], b in aa and a subseteq b implies a in aa)
      implies
     forall(f:ff, rel%failure_q(rel%part(f,aa),aa)))"
  lemma
  (theory directed-monoid-theory)
  (proof
   (


    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    (cut-with-single-formula "failure_q(f)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises ff-in-quasi-sort_directed-monoid-theory)
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(f:ff,failure_q(f));")
      (unfold-single-defined-constant-globally failure_q)
      (unfold-single-defined-constant-globally support)
      (apply-macete-with-minor-premises indicator-facts-macete)
      beta-reduce-repeatedly
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 0 0 0 0 0)")
	(backchain "with(p:prop,forall(u_$0:uu,x_$8,y_$0:sets[action],p));")
	auto-instantiate-existential)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 1 0 0 0 0)")
	(backchain "with(p:prop,forall(b,a:sets[action],p));")
	auto-instantiate-existential)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0)")
	simplify-insistently
	(instantiate-existential ("empty_indic{action}"))
	(apply-macete-with-minor-premises rev%failure-non-empty-condition)
	auto-instantiate-existential)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 2 0 0 0 0 0 0 0)")
	(instantiate-universal-antecedent "with(p:prop,forall(u_$0,v_$0:uu,p));"
					  ("u_$0" "v_$0"))
	(block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 0 0)")
	  (instantiate-universal-antecedent "with(f:sets[sets[action]],empty_indic_q{f});"
					    ("x_$1"))
	  (simplify-antecedent "with(x_$1:sets[action],aa:sets[sets[action]],u_$0:uu,f:ff,
  x_$1 in f(u_$0) inters aa);"))
	(block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
	  simplify-insistently
	  (instantiate-existential ("empty_indic{action}"))
	  (apply-macete-with-minor-premises rev%failure-non-empty-condition)
	  auto-instantiate-existential))
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 3 0 0 0 0 0 0 0
0 0 0 0)")
	(instantiate-universal-antecedent "with(p:prop,forall(u_$0:uu,a_$0:action,p));"
					  ("u_$0" "a_$0"))
	(block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	  (instantiate-universal-antecedent "with(f:sets[sets[action]],empty_indic_q{f});"
					    ("x_$1"))
	  (simplify-antecedent "with(x_$1:sets[action],aa:sets[sets[action]],u_$0:uu,f:ff,
  x_$1 in f(u_$0) inters aa);"))
	(block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0 0 0)")
	  (instantiate-universal-antecedent "with(p:prop,forall(m_$0:uu,p or p));"
					    ("m_$0"))
	  (contrapose "with(f:sets[sets[action]],empty_indic_q{f});")
	  (instantiate-existential ("empty_indic{action}"))
	  simplify-insistently
	  (apply-macete-with-minor-premises rev%failure-non-empty-condition)
	  auto-instantiate-existential)
	(backchain "with(p:prop,forall(x_$8:sets[action],p));"))
      (backchain "with(p:prop,forall(x:action,a:sets[action],p));")
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 4 0 0 0)")
	insistent-direct-inference
	simplify)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 5 0 0 0 0 0 0)")
	simplify-insistently
	(backchain "with(p:prop,forall(u_$0:uu,s_$0:sets[action],p));")
	auto-instantiate-existential)
      simplify-insistently)

    )))


(def-language relativized-graded-monoid
  (embedded-languages  graded-monoid)
  (constants (aa "sets[sets[action]]")))


(def-theory relativized-graded-monoid
  (component-theories  graded-monoid)
  (language  relativized-graded-monoid)
  (axioms
   (non-vacuous "empty_indic{action} in aa")
   (closure-under-unions-with-finite-sets
     "forall(x:action, a:sets[action], 
        a in aa implies a union singleton{x} in aa)")
   (hereditary-property
    "forall(b,a:sets[action], b in aa and a subseteq b implies a in aa)")))
     
(def-theorem ()
  "lambda(f:ff, rel%failure_q(f,aa))(rel%part(stop_ff,aa))"
  (theory relativized-graded-monoid) 
  (proof
   (


    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory)
    (cut-with-single-formula "rel%failure_q(rel%part(stop_ff,aa),aa)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (incorporate-antecedent "with(p:prop,p);")
     (unfold-single-defined-constant (0) rel%failure_q)
     direct-and-antecedent-inference-strategy)
    (block 
     (script-comment "`beta-reduce-with-minor-premises' at (1 0 1)")
     (apply-macete-with-minor-premises rel%part-mapping-property)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      direct-and-antecedent-inference-strategy
      (apply-macete-with-minor-premises non-vacuous)
      (apply-macete-with-minor-premises closure-under-unions-with-finite-sets)
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (2 0 0 0)")
       (apply-macete-with-minor-premises hereditary-property)
       auto-instantiate-existential))
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (apply-macete-with-minor-premises 
       ff-defining-axiom_directed-monoid-theory)
      (apply-macete-with-minor-premises stop-is-a-failure)))
    )))

(def-atomic-sort ff_aa
  "lambda(f:ff, rel%failure_q(f,aa))"
  (theory relativized-graded-monoid)
  (witness "rel%part(stop_ff,aa)"))

(def-constant rel_aa
  "lambda(f:ff, rel%part(f,aa))"
   (theory relativized-graded-monoid))

(def-theorem rel_aa-is-non-expansive   
  "forall(f,g:ff, fn%dist(rel_aa(f),rel_aa(g))<=fn%dist(f,g))"
  lemma
  (theory  relativized-graded-monoid)
  (usages transportable-macete)
  (proof
   (

    direct-inference
    (cut-with-single-formula
     "forsome(u,v,w,x:total%fns, rel_aa(f)=u and rel_aa(g)=v and f=w and g=x)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,p);")
     (backchain-repeatedly ("with(x,w,v:total%fns,g:ff,u:total%fns,f:ff,
  rel_aa(f)=u and rel_aa(g)=v and f=w and g=x);"))
     (apply-macete-with-minor-premises tr%characterization-of-non-expansiveness)
     (backchain-backwards "with(p:prop,p);")
     (backchain-backwards "with(p:prop,p);")
     (backchain-backwards "with(p:prop,p);")
     (backchain-backwards "with(p:prop,p);")
     (weaken (0))
     (unfold-single-defined-constant-globally rel_aa)
     (unfold-single-defined-constant-globally rel%part)
     (unfold-single-defined-constant-globally fn%approx)
     direct-and-antecedent-inference-strategy
     beta-reduce-with-minor-premises
     (move-to-sibling 1)
     (block 
      (script-comment "`beta-reduce-with-minor-premises' at (1)")
      (apply-macete-with-minor-premises total%fns-defining-axiom_graded-monoid)
      beta-reduce-repeatedly
      insistent-direct-inference
      beta-reduce-repeatedly)
     (move-to-sibling 2)
     (block 
      (script-comment "`beta-reduce-with-minor-premises' at (2)")
      (apply-macete-with-minor-premises total%fns-defining-axiom_graded-monoid)
      beta-reduce-repeatedly
      insistent-direct-inference
      beta-reduce-repeatedly)
     (block 
      (script-comment "`beta-reduce-with-minor-premises' at (0)")
      direct-and-antecedent-inference-strategy
      beta-reduce-repeatedly
      simplify))
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (instantiate-existential ("rel_aa(f)" "rel_aa(g)" "f" "g"))
     (block 
      (script-comment "`instantiate-existential' at (0 0)")
      simplify
      (unfold-single-defined-constant (0) rel_aa)
      (unfold-single-defined-constant (0) rel%part))
     (block 
      (script-comment "`instantiate-existential' at (0 1)")
      simplify
      (unfold-single-defined-constant (0) rel_aa)
      (unfold-single-defined-constant (0) rel%part))
     (block 
      (script-comment "`instantiate-existential' at (1)")
      (apply-macete-with-minor-premises total%fns-defining-axiom_graded-monoid)
      beta-reduce-repeatedly
      insistent-direct-inference
      (unfold-single-defined-constant (0) rel_aa)
      (unfold-single-defined-constant (0) rel%part))
     (block 
      (script-comment "`instantiate-existential' at (2)")
      (apply-macete-with-minor-premises total%fns-defining-axiom_graded-monoid)
      beta-reduce-repeatedly
      insistent-direct-inference))


    )))


;;We now consider finite failures

(load-section basic-cardinality)

(def-constant f_indic_act
  "indic{x:sets[action], f_indic_q{x}}"
  (theory graded-monoid))

(def-theorem ()
  "empty_indic{action} in f_indic_act"
  lemma
  (theory graded-monoid)
  (proof
   (

    (unfold-single-defined-constant (0) f_indic_act)
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (instantiate-existential ("0"))
    (apply-macete-with-minor-premises tr%empty-indic-has-f-card-zero)


    )))

(def-theorem finite-closure-under-singleton-lemma
  "forall(a:sets[action],
  a in f_indic_act
   implies 
  forall(x:action,
       a union singleton{x} in f_indic_act))"
  lemma
  (theory graded-monoid)
  (proof
   (


    (unfold-single-defined-constant-globally f_indic_act)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    direct-and-antecedent-inference-strategy
    (case-split ("x in a"))
    (block 
     (script-comment "`case-split' at (1)")
     (instantiate-existential ("n"))
     (cut-with-single-formula "a union singleton{x}=a")
     (move-to-sibling 1)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
      direct-and-antecedent-inference-strategy
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
       simplify-insistently
       direct-and-antecedent-inference-strategy
       simplify)
      simplify-insistently)
     simplify)
    (block 
     (script-comment "`case-split' at (2)")
     (apply-macete-with-minor-premises tr%f-card-disjoint-union)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (instantiate-existential ("n+1"))
      (apply-macete-with-minor-premises tr%singleton-has-f-card-one-rewrite)
      simplify)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
      (instantiate-existential ("1"))
      (apply-macete-with-minor-premises tr%singleton-has-f-card-one-rewrite))
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (2)")
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (contrapose "with(p:prop,not(p));")
      (backchain-backwards "with(x,x_$0:action,x_$0=x);")))

    )))

(def-theorem ()
  "forall(a:sets[action],
  a in f_indic_act
   implies 
  forall(x:action,
    lambda(x_$2:action,
      if(x_$2 in a or x_$2=x, an%individual, ?unit%sort))
     in f_indic_act))"
  lemma
  (theory graded-monoid)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "lambda(x_$2:action,
    if(x_$2 in a or x_$2=x, an%individual, ?unit%sort))=a union singleton{x}")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (backchain "with(f:sets[action],f=f);")
     (apply-macete-with-minor-premises finite-closure-under-singleton-lemma))
    simplify
    )))

(def-theorem ()
  "forall(a:sets[action],
    forsome(b:sets[action],b in f_indic_act and a subseteq b)
     implies 
    a in f_indic_act)"
  lemma
  (theory graded-monoid)
  (proof
   (

    (unfold-single-defined-constant-globally f_indic_act)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential


    )))
 
(def-translation finite-specialization-of-rgm
  (source relativized-graded-monoid)
  (target graded-monoid)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs (aa f_indic_act))
  (theory-interpretation-check using-simplification))

(def-constant extendable
  "lambda(f:[uu -> sets[sets[action]]], u:uu, a:action,
     forsome(m:uu, germ(m)=a and (u**m) in support(f)))"
  (theory graded-monoid))

(def-theorem failure-property
  "forall(f:ff, u:uu, a:action, u in support(f) and not extendable(f,u,a) 
    implies
   forall(x:sets[action], x in f(u) implies  (x union singleton{a}) in f(u)))"
  lemma
  (theory graded-monoid)
  (proof
   (


    (unfold-single-defined-constant-globally extendable)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "failure_q(f)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (incorporate-antecedent "with(f:ff,failure_q(f));")
     (unfold-single-defined-constant-globally failure_q)
     direct-and-antecedent-inference-strategy
     simplify)
    (apply-macete-with-minor-premises ff-in-quasi-sort_directed-monoid-theory)

    )))

(def-theorem finite-non-extendable-sets-may-be-added-to-refusal-sets
  "forall(f:ff, u:uu, s,s_1:sets[action], 
     u in support(f) and 
     f_indic_q{s} and 
     s_1 in f(u) and
     forall(a:action, a in s implies not(extendable(f,u,a))) implies 
     s union s_1 in f(u))"
  (theory  graded-monoid)
  (proof
   (


    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(n:zz, 
    0<=n 
      implies 
    forall(s:sets[action], 
     f_card{s}=n and
     forall(a:action, a in s  implies  not(extendable(f_$0,u,a)))
       implies s  union s_1 in f_$0(u)))")
    simplify
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (weaken (3 0))
     (induction trivial-integer-inductor ("n"))
     (block 
      (script-comment "`induction' at (0 0)")
      beta-reduce-repeatedly
      (apply-macete-with-minor-premises tr%empty-indic-has-f-card-zero)
      direct-and-antecedent-inference-strategy
      (backchain "with(f,s:sets[action],s=f);")
      (apply-macete-with-minor-premises tr%union-commutativity)
      (apply-macete-with-minor-premises tr%union-with-empty))
     (block 
      (script-comment "`induction' at (0 1 0 0 0 0 0 0 0)")
      (cut-with-single-formula "forsome(x:action, x in s )")
      (antecedent-inference "with(s:sets[action],nonempty_indic_q{s});")
      (cut-with-single-formula "s= (s diff singleton{x}) union singleton{x}")
      (cut-with-single-formula "f_card{s diff singleton{x}}=t")
      (instantiate-universal-antecedent "with(p:prop,forall(s:sets[action],p));"
					("s diff singleton{x}"))
      (block 
       (script-comment "`instantiate-universal-antecedent' at (0 0 0 1 0 0)")
       (instantiate-universal-antecedent "with(p:prop,forall(a:action,p));"
					 ("a_$0"))
       (contrapose "with(p:prop,not(p));")
       (incorporate-antecedent "with(a_$0:action,f,s:sets[action],a_$0 in s diff f);")
       simplify-insistently)
      (block 
       (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
       (backchain "with(f,s:sets[action],s=f);")
       (force-substitution "(s diff singleton{x}) union singleton{x} union s_1"
			   "((s diff singleton{x}) union s_1) union singleton{x} "
			   (0))
       (block 
	(script-comment "`force-substitution' at (0)")
	(apply-macete-with-minor-premises failure-property)
	direct-and-antecedent-inference-strategy
	simplify)
       (move-to-ancestor 6)
       (move-to-descendent (1))
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(cut-with-single-formula "f_indic_q{s}")
	(incorporate-antecedent "with(r:rr,n:nn,n=r);")
	(backchain "with(f,s:sets[action],s=f);")
	(apply-macete-with-minor-premises tr%f-card-disjoint-union)
	(block 
	 (script-comment "`apply-macete-with-minor-premises' at (0)")
	 (apply-macete-with-minor-premises tr%singleton-has-f-card-one-rewrite)
	 simplify)
	(block 
	 (script-comment "`apply-macete-with-minor-premises' at (1)")
	 (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
	 (apply-macete-with-minor-premises tr%singleton-has-f-card-one-rewrite)
	 (instantiate-existential ("1")))
	(block 
	 (script-comment "`apply-macete-with-minor-premises' at (2)")
	 (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
	 auto-instantiate-existential
	 simplify-insistently)
	simplify-insistently)
       (move-to-ancestor 7)
       (move-to-descendent (1))
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	direct-and-antecedent-inference-strategy
	simplify-insistently
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	 simplify-insistently
	 direct-and-antecedent-inference-strategy
	 simplify))
       (move-to-ancestor 9)
       (move-to-descendent (1))
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises tr%rev%positive-f-card-iff-nonempty)
	simplify)
       (block 
	(script-comment "`force-substitution' at (1)")
	simplify
	(apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	direct-and-antecedent-inference-strategy
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	 simplify-insistently
	 direct-and-antecedent-inference-strategy)
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	 simplify-insistently
	 direct-and-antecedent-inference-strategy
	 (contrapose "with(p:prop,not(p));")
	 (backchain "with(x,x_$1:action,x_$1=x);"))))))

    )))


(def-theorem finite-non-extendable-sets-may-be-refused
  "forall(f:ff, u:uu, s:sets[action], 
     u in support(f) and 
     f_indic_q{s} and 
     forall(a:action, a in s implies not(extendable(f,u,a))) implies 
     s in f(u))"
  (theory  graded-monoid)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (force-substitution "s" "s union empty_indic{action}" (0))
    (block 
     (script-comment "`force-substitution' at (0)")
     (apply-macete-with-minor-premises finite-non-extendable-sets-may-be-added-to-refusal-sets)
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises rev%failure-non-empty-condition)
     (incorporate-antecedent "with(u:uu,f:sets[uu],u in f);")
     (unfold-single-defined-constant (0) support)
     simplify)
    (apply-macete-with-minor-premises tr%union-with-empty)


    )))


(def-renamer fs-rgm-renamer
 (pairs 
  (ff_aa ff_fin)
  (rel_aa rel_fin)))


(def-transported-symbols (ff_aa rel_aa)
  (translation finite-specialization-of-rgm)
  (renamer fs-rgm-renamer))

(def-theorem rel_fin-is-non-expansive   
  "forall(f,g:ff, fn%dist(rel_fin(f),rel_fin(g))<=fn%dist(f,g))"
  (theory  graded-monoid)
  (proof
   (

    (apply-macete-with-minor-premises tr%rel_aa-is-non-expansive)

    )))
