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


(herald hoare-machines)
(load-section sequences)

;;(set (proof-log-port) (standard-output))
;; 

(def-language hoare-machine-language
  (base-types state action)
  (constants 
   (tr (state action state prop))
   (initial (state prop))))

(def-theory hoare-machines
  (language hoare-machine-language)
  (component-theories h-o-real-arithmetic))

;;; Definitions

(def-constant unrefused
  "lambda(s:state,a:action, forsome(s_1:state, tr(s,a,s_1)))"
  (theory hoare-machines))

(def-theorem unrefused-actions-have-transitions
  "forall(s:state, a:action,
     unrefused(s,a) iff forsome(s_1:state, tr(s,a,s_1)))"
  (proof 
   (
    unfold-defined-constants
    ))
  (theory hoare-machines))

(def-constant  history
  "lambda(s_seq:[nn,state], a_seq:[nn,action],
        (#(s_seq(0)) implies initial(s_seq(0)))
       and
	forall(i:nn, (#(a_seq(i)) implies unrefused(s_seq(i),a_seq(i)))
		and (#(s_seq(1+i)) implies tr(s_seq(i),a_seq(i),s_seq(1+i)))))"  
  (theory hoare-machines)
  (usages transportable-macete))

(def-constant  accessible
  "lambda(s:state,
	forsome(s_seq:[nn,state], a_seq:[nn,action], i:nn,
	 history(s_seq, a_seq) and s_seq(i)=s))"  
  (theory hoare-machines)
  (usages transportable-macete))


(def-imported-rewrite-rules  hoare-machines
 (source-theories sequences))

(def-theorem h-histories-defined-on-state-segment
 "forall(s_seq:[nn,state], a_seq:[nn,action], i,j:zz,
history(s_seq, a_seq) and #(s_seq(j)) and i<=j and 0<=i implies #(s_seq(i)))"
 (theory hoare-machines)
 (usages transportable-macete)
 (proof
  (
   (unfold-single-defined-constant-globally history)
   direct-and-antecedent-inference-strategy
   (move-to-ancestor 1)
   (contrapose "with(s:state,#(s));")
   (induction integer-inductor ("j"))
   (antecedent-inference-strategy (2))
   (backchain "with(p:prop,forall(i:nn,p));")
   simplify)))

(def-theorem h-histories-defined-at-state-predecessor
  "forall(s_seq:[nn,state], a_seq:[nn,action], i:zz,
history(s_seq, a_seq) and #(s_seq(1+i)) and 0<=i implies #(s_seq(i)))"
  (theory hoare-machines)
  (proof
   (


    (apply-macete-with-minor-premises h-histories-defined-on-state-segment)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("1+i" "a_seq"))
    simplify

    ))
  (usages transportable-macete))



(def-theorem h-histories-defined-on-state-segment-nn
  "forall(s_seq:[nn,state], a_seq:[nn,action], i:nn,j:zz,
history(s_seq, a_seq) and #(s_seq(j)) and i<=j  implies #(s_seq(i)))"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally history)
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 1)
    (contrapose "with(s:state,#(s));")
    (induction integer-inductor ("j"))
    (antecedent-inference "with(p:prop,not(p) implies not(p));")
    (backchain "with(p:prop,forall(i:nn,p));")
    simplify
    (cut-with-single-formula "0<=i")
    simplify
    simplify)))



(def-theorem h-histories-defined-on-action-segment
  "forall(s_seq:[nn,state], a_seq:[nn,action], i,j:zz,
history(s_seq, a_seq) and #(s_seq(j+1)) and i<=j and 0<=i implies #(a_seq(i)))"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally history)
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 1)
    (contrapose "with(s:state,#(s));")
    (induction integer-inductor ("j"))
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,forall(i:nn,p));")
    simplify
    (force-substitution "2+t" "1+(1+t)" (0))
    (backchain "with(p:prop,forall(i:nn,p));")
    (antecedent-inference-strategy (2))
    simplify
    simplify)))

(def-theorem h-histories-defined-at-0
  "forall(s_seq:[nn,state], a_seq:[nn,action], j:zz,
history(s_seq, a_seq) and #(s_seq(j)) implies #(s_seq(0)))"
  (theory hoare-machines)
  
  (proof
   (
    (apply-macete-with-minor-premises h-histories-defined-on-state-segment)
    simplify
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    simplify)))

(def-theorem h-history-at-0-is-initial
  "forall(s_seq:[nn,state], a_seq:[nn,action], j:zz,
history(s_seq, a_seq) and #(s_seq(j)) implies initial(s_seq(0)))"
   (theory hoare-machines)
 
 (proof
  (
   (unfold-single-defined-constant-globally history)
   direct-and-antecedent-inference-strategy
   (move-to-ancestor 1)
   (backchain "with(p:prop,p implies p);")
   (apply-macete-with-minor-premises h-histories-defined-at-0)
   (unfold-single-defined-constant-globally history)
   auto-instantiate-existential)))

(def-theorem h-accessible-lemma
  "forall(p:[state,prop],s:state,i:nn,s_seq:[nn,state], 
     s_seq(i)=s 
    implies
    (forall(j:zz, 0<=j and j<=i 
 	implies
	 p(s_seq(j))) 
	implies
         p(s)))"
  (theory hoare-machines)
  
  (proof (
	  direct-and-antecedent-inference-strategy
	  (backchain-backwards "with(s:state,s=s);")
	  (backchain "with(p:prop,forall(j:zz,p));")
	  simplify)))

(def-theorem h-sm-induction-forward
  "forall(p:[state,prop], 
      forall(s:state, initial(s) implies p(s))
     and
      forall(s_1,s_2:state,a:action, p(s_1) and tr(s_1,a,s_2) implies p(s_2)) 
    implies
      forall(s:state, accessible(s) implies p(s)));"
  (theory hoare-machines)
  
  (proof
   (
    (block
      (script-comment
       "first unfold the definitions and eliminate s in favor of s_seq(i)")
      (unfold-single-defined-constant-globally accessible)
      (unfold-single-defined-constant-globally history)
      direct-and-antecedent-inference-strategy
      (move-to-ancestor 2)
      (backchain-backwards "with(s:state,s=s);"))
    (block
      (script-comment
       "now introduce the i.h., backchain+simplify to discharge the main goal.")
      (cut-with-single-formula "forall(j:zz, 0<=j and #(s_seq(j)) implies p(s_seq(j)))")
      (backchain "with(p:prop,forall(j:zz,p implies p));")
      simplify)
    (induction integer-inductor ())
    (block
      (script-comment
       "for the base case, backchain on initial states having p.")
      direct-inference
      (backchain "with(p:prop,forall(s:state,p));")
      simplify)
    (block
      (script-comment
       "for the induction step case, backchain on the preservation clause.")
      (backchain "with(p:prop,forall(s_1,s_2:state,a:action,p));")
      (instantiate-existential ("s_seq(t)" "a_seq(t)"))
      (move-to-ancestor 2)
      (move-to-descendent (1 0))
      (block (script-comment "observe that s_seq(t) is well-defined.")
	     (apply-macete-with-minor-premises h-histories-defined-on-state-segment)
	     (instantiate-existential ("1+t" "a_seq"))
	     (unfold-single-defined-constant-globally history)
	     direct-and-antecedent-inference-strategy
	     simplify)
      (move-to-ancestor 2)
      (move-to-descendent (2 0))
      (block (script-comment "observe that a_seq(t) is well-defined.")
	     (apply-macete-with-minor-premises h-histories-defined-on-action-segment)
	     (instantiate-existential ("t" "s_seq"))
	     simplify)
      (backchain "with(p:[state,prop],t:zz,s_seq:[nn,state],
  #(s_seq(t)) implies p(s_seq(t)));")
      (backchain "with(p:prop,forall(i:nn,p));")))))


(def-theorem h-initial-implies-accessible
  "forall(s:state, initial(s) implies accessible(s))"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally accessible)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("seq{s,state}" "nil{action}" "0"))
    (unfold-single-defined-constant-globally history)
    simplify
    simplify)))

(def-theorem h-tr-preserves-accessible
 "forall(s_1,s_2:state, a:action, 
  accessible(s_1) and tr(s_1,a,s_2) implies accessible(s_2))"
 (theory hoare-machines)
 (usages transportable-macete)
 (proof
  (
   (unfold-single-defined-constant-globally accessible)
   direct-and-antecedent-inference-strategy
   (instantiate-existential
    (
     "lambda(j:nn, if(j<=i,s_seq(j),j=i+1,s_2,?state))"
     "lambda(j:nn, if(j<i,a_seq(j),j=i,a,?action))"
     "i+1"))
   (move-to-sibling 1)
   simplify
   (incorporate-antecedent "with(a_seq:[nn,action],s_seq:[nn,state],
  history(s_seq,a_seq));")
   (unfold-single-defined-constant-globally history)
   simplify
   direct-and-antecedent-inference-strategy
   (move-to-ancestor 1)
   (case-split ("i_$0<i" "i_$0=i"))
   simplify
   simplify
   (apply-macete-with-minor-premises unrefused-actions-have-transitions)
   auto-instantiate-existential
   (incorporate-antecedent "with(a:action,#(a));")
   simplify
   (move-to-ancestor 1)
   (case-split ("i_$0<i" "i_$0=i"))
   simplify
   simplify
   (incorporate-antecedent "with(s:state,#(s));")
   simplify)))

;;  


(def-theorem hsm-induction
 "forall(p:[state,prop],
  forall(s:state,initial(s) implies p(s))
   and 
  forall(s_1,s_2:state,a:action,
    accessible(s_1) and p(s_1) and tr(s_1,a,s_2)
     implies 
    p(s_2))
   implies 
  forall(s:state,accessible(s) implies p(s)));"
 (theory hoare-machines)
 
 (proof
  (
   (block
     (script-comment
      "first unfold the definitions and eliminate s in favor of s_seq(i)")
     (unfold-single-defined-constant-globally accessible)
     (unfold-single-defined-constant-globally history)
     direct-and-antecedent-inference-strategy
     (move-to-ancestor 2)
     (backchain-backwards "with(s:state,s=s);"))
   (block
     (script-comment
      "now introduce the i.h. backchain+simplify to discharge the main goal.")
     (cut-with-single-formula
      "forall(j:zz, 0<=j and #(s_seq(j)) implies p(s_seq(j)))")
     (backchain "with(p:prop,forall(j:zz,p implies p));")
     simplify)
   (induction integer-inductor ())
   (block
     (script-comment
      "for the base case, backchain on initial states having p.")
     direct-inference
     (backchain "with(p:prop,forall(s:state,p));")
     simplify)
   (block
     (script-comment
      "For the ind. step, backchain on preservation again.")
     (backchain "with(p:prop,forall(s_1,s_2:state,a:action,p));")
     (instantiate-existential ("(s_seq(t))" "(a_seq(t))"))
     (instantiate-existential ("s_seq" "a_seq" "t"))
     (let-script
      apply-macete-and-instantiate
      ;; macete name, sequence index, and other sequence.
      3
      ((if (progresses?
	    (apply-macete-with-minor-premises $1))
	   (block
	     (instantiate-existential ($2 $3))
	     (unfold-single-defined-constant-globally history)
	     simplify)
	   (skip))))
     (jump-to-node induction-step)
     (for-nodes 
      (unsupported-descendents)
      (block
	simplify
	($apply-macete-and-instantiate
	 h-histories-defined-on-state-segment "1+t" "a_seq")
	($apply-macete-and-instantiate
	 h-histories-defined-on-action-segment "t" "s_seq")))))))

(def-theorem hsm-induction-biconditional
  "forall(p:[state,prop],
	 forall(s:state, accessible(s) implies p(s))
	iff
	(forall(s:state, initial(s) implies p(s))
	and
	 forall(s_1, s_2:state, a:action,
		(accessible(s_1) and p(s_1) and tr(s_1, a, s_2))
		implies
		p(s_2))))"
 (theory hoare-machines)
 
 (proof
  (
   direct-inference
   direct-inference
   (block
     (script-comment "This is the easy direction.")
     direct-and-antecedent-inference-strategy
     (backchain "with(p:prop,forall(s:state,p));")
     (apply-macete-with-minor-premises h-initial-implies-accessible)
     (backchain "with(p:[state,prop],
  forall(s:state,accessible(s) implies p(s)));")
     (apply-macete-with-minor-premises h-tr-preserves-accessible)
     auto-instantiate-existential)
   (block
     (script-comment
      "This is the hard direction, but we've already done the work.")
     (instantiate-theorem hsm-induction ("p"))
     simplify))))

(def-inductor hsm-induct
  hsm-induction-biconditional
  (theory hoare-machines)
  (base-case-hook eliminate-nonrecursive-definitions-and-simplify))

(def-theorem history-state-length
  "forall(s_seq:[nn,state],a_seq:[nn,action], i:nn,
	history(s_seq,a_seq) and #(a_seq(i))
	implies #(s_seq(i)))"
  (theory hoare-machines)
  (proof
   (
    (unfold-single-defined-constant-globally history)
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 1)
    (instantiate-universal-antecedent "with(p:prop,forall(i:nn,p));" ("i"))))
  (usages transportable-macete))

;; Verbatim the same proof
;; 

(def-theorem history-action-length
  "forall(s_seq:[nn,state],a_seq:[nn,action], i:nn,
	history(s_seq,a_seq) and #(s_seq(1+i))
	implies #(a_seq(i)))"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally history)
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 1)
    (instantiate-universal-antecedent "with(p:prop,forall(i:nn,p));" ("i")))))

(def-theorem histories-extensible
  "forall(s_seq:[nn,state],a_seq:[nn,action], a:action, s:state, i:nn,
	(history(s_seq,a_seq)
	and tr(s_seq(i),a,s))
	implies 
	history(
	 lambda(j:nn, if(j<=i,s_seq(j),
			 j=i+1,s,?state)),
	 lambda(j:nn, if(j<i,a_seq(j),
			 j=i,a,?action))))"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally history)
    direct-inference-strategy
    (move-to-ancestor 1)
    simplify
    (move-to-ancestor 2)
    (case-split-on-conditionals (0 1))
    (apply-macete-with-minor-premises unrefused-actions-have-transitions)
    (instantiate-existential ("s")))))


(def-recursive-constant accessible%from
  "lambda(rec:[state, state, prop],
     lambda(s_0,s_2:state, 
       s_0=s_2
        or 
       forsome(s_1:state, a:action, rec(s_0,s_1) and tr(s_1,a,s_2))))"
  (definition-name accessible%from)
  (theory hoare-machines))

(def-print-syntax accessible%from
  TEX
  (token " \\preceq ") ; a symbol or string.
  (method present-tex-binary-infix-operator) 
  (binding 80))

(def-theorem accessible%from-reflexive
  "forall(s_0:state,accessible%from(s_0,s_0))"
  (theory hoare-machines)
  (proof ((unfold-single-defined-constant-globally accessible%from)))
  (usages rewrite))

(def-theorem accessible%from-cases
  "forall(s_0,s_1:state,accessible%from(s_0,s_1) implies 
    (s_0=s_1 or forsome(s:state, a:action, accessible%from(s_0,s) and tr(s,a,s_1))))"
  (theory hoare-machines)
  (proof ((unfold-single-defined-constant (0) accessible%from)))
  (usages transportable-macete))

(def-theorem a%f-induction-conv
  "forall(p:[state,prop],s_0:state,
    forall(s_1:state, accessible%from(s_0,s_1) implies p(s_1))
      implies
    (p(s_0) 
     and
     forall(s_1,s_2:state, a:action, 
      accessible%from(s_0,s_1) and tr(s_1,a,s_2) and p(s_1)
    implies p(s_2))))"
  (theory hoare-machines)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,p);" ("s_0"))
    (contrapose "with(p:prop,p);")
    simplify
    (instantiate-universal-antecedent
     "with(p:prop,forall(s_1:state,p));" ("s_2"))
    (contrapose "with(p:prop,not(p));")
    (unfold-single-defined-constant-globally accessible%from)
    direct-inference
    auto-instantiate-existential)))
  

(def-theorem a%f-induction
   "forall(p:[state,prop],s_0:state,
  p(s_0)
   and 
  forall(s_1,s_2:state,a:action,
    accessible%from(s_0,s_1) and tr(s_1,a,s_2) and p(s_1)
     implies 
    p(s_2))
   implies 
  forall(s_1:state,accessible%from(s_0,s_1) implies p(s_1)));"
   (theory hoare-machines)
   (proof
    (
     direct-inference
     (instantiate-theorem accessible%from-strong-minimality_hoare-machines
			  ("lambda(u_0,u_1:state, s_0=u_0 implies (accessible%from(s_0,u_1) and p(u_1)))"))
     (move-to-ancestor 4)
     (move-to-descendent (1))
     (block
       (script-comment "First use the consequent of minimality.")
       (simplify-antecedent "with(p:prop,p);")
       (unfold-single-defined-constant (1) accessible%from)
       direct-and-antecedent-inference-strategy
       simplify
       (auto-instantiate-universal-antecedent "with(p:[state,prop],s_0:state,
  forall(u_1:state,
    not(accessible%from(s_0,u_1))
     or 
    accessible%from(s_0,u_1) and p(u_1)));")
       (backchain "with(p:prop,forall(s_1,s_2:state,a:action,p));")
       auto-instantiate-existential)
     (move-to-ancestor 1)
     (block
       (script-comment "Next prove the antecedent of minimality.")
       
       (simplify-antecedent "with(p:prop,not(p));")
       (simplify-antecedent "with(p:prop,p or p);")
       (antecedent-inference-strategy (0 1))
       (contrapose "with(p:prop,not(p));")
       simplify
       simplify
       (contrapose "with(p:prop,not(p));")
       (unfold-single-defined-constant-globally accessible%from)
       direct-inference
       (instantiate-existential ("s_1" "a"))
       (contrapose "with(p:prop,not(p));")
       (antecedent-inference "with(p:prop,p and p and p);")
       (auto-instantiate-universal-antecedent "with(p:[state,prop],s_0:state,
  forall(s_1,s_2:state,a:action,
    accessible%from(s_0,s_1) and tr(s_1,a,s_2) and p(s_1)
     implies 
    p(s_2)));")))))


(def-theorem a%f-induction-bi
  "forall(p:[state,prop],s_0:state,
    forall(s_1:state, accessible%from(s_0,s_1) implies p(s_1))
      iff
    (p(s_0) 
     and
     forall(s_1,s_2:state, a:action, 
      accessible%from(s_0,s_1) and tr(s_1,a,s_2) and p(s_1) 
    implies  p(s_2))))"
  (theory hoare-machines)
  (proof
   (
    direct-inference
    direct-inference
    (apply-macete-with-minor-premises a%f-induction-conv)
    (assume-theorem a%f-induction)
    simplify)))

(def-inductor accessible%from-inductor
  a%f-induction-bi
  (theory hoare-machines)
  (base-case-hook simplify))

(def-theorem accessible-states-accessible%from-initial
  "forall(x_0:state,
    accessible(x_0)
     implies 
    forsome(s_0:state,
      initial(s_0) and accessible%from(s_0,x_0)))"
  (theory hoare-machines)
  (proof
   (
    (induction hsm-induct ("x_0"))
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    simplify
    auto-instantiate-existential
    auto-instantiate-existential
    auto-instantiate-existential))
  (usages transportable-macete))

(def-theorem accessible%from-preserves-accessible
  "forall(s_0,s_1:state,
  accessible(s_0) and accessible%from(s_0, s_1)
   implies
  accessible(s_1))"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (induction accessible%from-inductor ("s_1"))
    (apply-macete-with-minor-premises h-tr-preserves-accessible)
    auto-instantiate-existential
    simplify)))

(def-theorem accessible%from-initial-is-accessible
  "forall(s_1,s_0:state,
      initial(s_0) and accessible%from(s_0,s_1)
     implies 
    accessible(s_1))"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises accessible%from-preserves-accessible)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (apply-macete-with-minor-premises h-initial-implies-accessible))))

  
(def-theorem accessible%from-initial-equals-accessible
  "lambda(s:state,
     forsome(s_0:state,
       initial(s_0) and accessible%from(s_0,s)))=
   accessible;"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises accessible%from-initial-is-accessible)
    auto-instantiate-existential
    (apply-macete-with-minor-premises accessible-states-accessible%from-initial))))

(def-theorem accessible%from-transitivity
  "forall(s_0,s_1,s_2:state, accessible%from(s_0,s_1) and accessible%from(s_1,s_2)
    implies 
   accessible%from(s_0,s_2) )"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (induction accessible%from-inductor ("s_2"))
    direct-inference
    (instantiate-existential ("s_$0"))
    simplify
    auto-instantiate-existential)))


(def-theorem tr-implies-accessible%from
  "forall(s_0,s_1:state, a:action, tr(s_0,a,s_1) implies accessible%from (s_0,s_1))"
  (theory hoare-machines)
  (proof
   (
    (unfold-single-defined-constant-globally accessible%from)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    simplify))
  (usages transportable-macete))
  
(def-theorem tr+accessible%from
  "forall(s_0,s_1,s_2:state, a:action, tr(s_0,a,s_1) and accessible%from(s_1,s_2) 
    implies accessible%from(s_0,s_2))"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (induction accessible%from-inductor ("s_2"))
    (apply-macete-with-minor-premises tr-implies-accessible%from)
    simplify
    direct-inference
    auto-instantiate-existential
    direct-inference
    (instantiate-existential ("s_$0"))
    simplify
    auto-instantiate-existential)))

(def-theorem accessible%from+tr
  "forall(s_0,s_1,s_2:state, a:action, accessible%from(s_0,s_1) and tr(s_1,a,s_2) 
    implies accessible%from(s_0,s_2))"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant (1) accessible%from)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential)))


(def-constant state%history
  "lambda(s_seq:[nn,state], 
    forsome(a_seq:[nn,action], history(s_seq, a_seq)))"
  (theory hoare-machines))

(def-theorem state%histories-extensible
  "forall(s_seq:[nn,state],i:nn,a:action,s_f:state,
  state%history(s_seq)
   and 
  length{s_seq}=i+1
   and 
  tr(s_seq(i),a,s_f)
   implies 
  state%history(append{s_seq,seq{s_f,state}}));"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    unfold-defined-constants
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 1)
    (backchain-repeatedly ("with(i:nn,s_seq:[nn,state],length{s_seq}=i+1);"))
    (instantiate-existential ("lambda(j:nn, if(j<i,a_seq(j), j=i,a,?action))"))
    simplify
    (move-to-ancestor 1)
    (case-split-on-conditionals (2))
    (case-split-on-conditionals (0))
    (cut-with-single-formula "(i_$1=i)")
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises unrefused-actions-have-transitions)
    auto-instantiate-existential
    (move-to-ancestor 1)
    simplify
    (case-split ("i_$1<i"))
    simplify
    (case-split-on-conditionals (1)))))

(def-theorem state%histories-extensible-1
  "forall(s_seq:[nn,state],i:nn,a:action,s_f:state,
  state%history(s_seq)
   and 
  tr(s_seq(length{s_seq}-1),a,s_f)
   implies 
  state%history(append{s_seq,seq{s_f,state}}));"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises state%histories-extensible)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    simplify)))

;; (!)

(def-theorem state%history-subsequence
  "forall(s_seq_1, s_seq_2:[nn,state],
  state%history(append{s_seq_1, s_seq_2})
   implies 
  state%history(s_seq_1));"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (


    direct-inference
    (case-split ("f_seq_q{s_seq_1}"))
    (move-to-sibling 2)
    (apply-macete-with-minor-premises tr%infinite-append)
    (case-split ("s_seq_1=nil{state}"))
    (block 
      (script-comment "`case-split' at (1)")
      simplify
      direct-inference
      (unfold-single-defined-constant-globally state%history)
      (instantiate-existential ("nil{action}"))
      (unfold-single-defined-constant-globally history))
    (cut-with-single-formula "1<=length{s_seq_1}")
    (move-to-sibling 1)
    (contrapose "with(p:prop,not(p));")
    (instantiate-transported-theorem length-0-implies-nil () ("s_seq_1"))
    (block 
      (script-comment "`instantiate-transported-theorem' at (0 0)")
      (contrapose "with(n:nn,not(1<=n));")
      simplify)
    (unfold-single-defined-constant-globally state%history)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("lambda(j:zz, if(j<length{s_seq_1}, a_seq(j), ?action))"))
    (unfold-single-defined-constant-globally history)
    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (block 
      (script-comment "`instantiate-existential' at (0 0 1)")
      sort-definedness
      direct-inference
      (case-split ("#(xx_0,zz)"))
      simplify
      simplify)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
      (incorporate-antecedent "with(a_seq:[nn,action],f:[nn,state],history(f,a_seq));")
      (unfold-single-defined-constant-globally history)
      direct-inference
      (antecedent-inference "with(p:prop,p and p);")
      (incorporate-antecedent "with(p:prop,p implies p);")
      simplify)
    simplify
    (move-to-ancestor 2)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0
0)")
      simplify
      (incorporate-antecedent "with(a_seq:[nn,action],f:[nn,state],history(f,a_seq));")
      (unfold-single-defined-constant-globally history)
      direct-inference
      (antecedent-inference "with(p:prop,p and p);")
      (instantiate-universal-antecedent "with(p:prop,forall(i:nn,p));"
					("i_$0"))
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0 0 0)")
	(contrapose "with(a:action,#(a));")
	simplify)
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0 0 1)")
	(incorporate-antecedent "with(a:action,s:state,unrefused(s,a));")
	simplify
	(move-to-ancestor 1)
	(case-split-on-conditionals (0))
	(contrapose "with(a:action,#(a));")
	simplify)
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0 1 1)")
	(incorporate-antecedent "with(a:action,s:state,unrefused(s,a));")
	(incorporate-antecedent "with(a:action,#(a));")
	(case-split-on-conditionals (1))))
    (move-to-ancestor 2)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 1 0)")
      (incorporate-antecedent "with(a_seq:[nn,action],f:[nn,state],history(f,a_seq));")
      (unfold-single-defined-constant-globally history)
      direct-inference
      (antecedent-inference "with(p:prop,p and p);")
      (instantiate-universal-antecedent "with(p:prop,forall(i:nn,p));"
					("i_$0"))
      (move-to-ancestor 2)
      (incorporate-antecedent "with(a:action,s:state,#(s) implies tr(s,a,s));")
      (case-split-on-conditionals (3))
      (move-to-ancestor 2)
      (move-to-descendent (2 0))
      (block 
	(script-comment "`case-split-on-conditionals' at (2 0)")
	(contrapose "with(s:state,#(s));")
	(apply-macete-with-minor-premises tr%meaning-of-length-rev)
	simplify)
      (block 
	(script-comment "`case-split-on-conditionals' at (1 0)")
	(cut-with-single-formula "1+i_$0<length{s_seq_1}")
	simplify
	(apply-macete-with-minor-premises tr%length-characterizes-definedness)))


    )))

(def-theorem state%histories-extensible-rev
  "forall(s_seq:[nn,state],i:nn,s_f:state,
  state%history(append{s_seq,seq{s_f,state}})
   implies 
  state%history(s_seq));"
  (theory hoare-machines)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises state%history-subsequence)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential)))

(def-theory-ensemble hoare-machines)

(def-language det-hoare-machine-language
  (base-types state action)
  (constants 
   (next (state action state))
   (initial (state prop))))
      
(def-theory det-hoare-machines
  (language det-hoare-machine-language)
  (component-theories h-o-real-arithmetic))

(def-theory-ensemble-instances hoare-machines
  (target-theories det-hoare-machines)
  (sorts 
   (state state)
   (action action))
  (constants
   (tr "lambda(s:state,a:action,s_1:state,next(s,a)=s_1)")
   (initial initial))
  (multiples 1))

(def-theorem unrefused-actions-have-next
  "forall(s:state, a:action, unrefused(s,a) iff #(next(s,a)))"
  (theory det-hoare-machines)
  (proof
   (
    (unfold-single-defined-constant-globally unrefused)
    simplify)))    

(def-recursive-constant run
  "lambda(r:[state,[nn,action],state],
       lambda(s:state,a_seq:[nn,action],
	if(a_seq=nil(action), s,
	   r(next(s,(a_seq(0))), drop(a_seq,1)))))"
  (theory det-hoare-machines)
  (usages 
   transportable-macete))

(def-imported-rewrite-rules det-hoare-machines
  (source-theories sequences))

(def-theorem h-next-preserves-accessible
  "forall(s,s_1:state, a:action, accessible(s) and next(s,a)=s_1
	 implies accessible(s_1))"
  (theory det-hoare-machines)
  (usages transportable-macete)
  (proof (
	  (apply-macete-with-minor-premises tr%h-tr-preserves-accessible)
	  simplify)))

(def-theorem h-run-next
  "forall(s_1:state,a:action,a_seq:[nn,action], 
 	run(next(s_1,a),a_seq)==run(s_1,cons(a,a_seq)))"
  (theory det-hoare-machines)
  (usages transportable-macete)
  ;; Unfold second occurrence and simplify.  
  (proof (
	  (unfold-single-defined-constant (1) run)
	  simplify)))


(def-inductor hsm->dhsm-inductor
  hsm-induction-biconditional
  (translation HOARE-MACHINES-TO-DET-HOARE-MACHINES)
  (theory det-hoare-machines)
  (base-case-hook simplify))

;;(!)

(def-theorem hdsm-induction-biconditional-conv
  "forall(p:[state,prop],  forall(s:state, accessible(s) implies p(s)) 
     iff
      (forall(s:state, initial(s)  implies p(s))
       and 
       forall(s_1:state,a:action, accessible(s_1) and p(s_1)
				  and #(next(s_1,a)) 
 	 implies p(next(s_1,a)))))"
  (theory det-hoare-machines)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    direct-inference
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,forall(s:state,p));")
    (apply-macete-with-minor-premises tr%h-initial-implies-accessible)
    (backchain "with(p:[state,prop],
  forall(s:state,accessible(s) implies p(s)));")
    (apply-macete-with-minor-premises h-next-preserves-accessible)
    (instantiate-existential ("a" "s_1"))
    (induction hsm->dhsm-inductor ("s"))
    (backchain-backwards "with(s_2,s:state,s=s_2);")
    (backchain "with(p:prop,forall(s_1:state,a:action,p));")
    simplify)))

(def-inductor hdsm-inductor
  hdsm-induction-biconditional-conv
  (theory det-hoare-machines)
  (base-case-hook simplify))

(def-translation sequences->hoare-actions 
  (source sequences)
  (target det-hoare-machines)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 action))
  (theory-interpretation-check using-simplification))

(def-inductor hdsm-act-inductor
  sequence-induction
  (theory det-hoare-machines)
  (translation sequences->hoare-actions)
  (base-case-hook eliminate-nonrecursive-definitions-and-simplify))

(def-theorem h-run-run-lemma
  "forall(a_seq_1:[nn,action], 
     f_seq_q(a_seq_1) implies
        forall(s_1:state, a_seq_2:[nn,action],
	run(run(s_1,a_seq_1),a_seq_2)==run(s_1, append(a_seq_1,a_seq_2))))"
  (theory det-hoare-machines)
  
  (proof
   (
    (induction hdsm-act-inductor ())
    (unfold-single-defined-constant (1) run)
    (unfold-single-defined-constant (2) run)
    simplify
    (case-split ("#(next(s_$0,e))"))
    simplify
    insistent-direct-and-antecedent-inference-strategy)))

(def-theorem h-run-run
  "forall(s_1:state, a_seq_1, a_seq_2:[nn,action], 
     f_seq_q(a_seq_1) implies
	run(run(s_1,a_seq_1),a_seq_2)==run(s_1, append(a_seq_1,a_seq_2)))"
  (theory det-hoare-machines)
  (usages transportable-macete)
  (proof ((apply-macete-with-minor-premises h-run-run-lemma))))

(def-theorem next-accessible%from-1 
  tr+accessible%from
  (theory det-hoare-machines)
  (proof existing-theorem)
  (translation hoare-machines-to-det-hoare-machines))

(def-theorem next-accessible%from
  "forall(s_0,s_1,s_2:state,a:action,
    accessible%from(next(s_0,a),s_2)
     implies 
    accessible%from(s_0,s_2));"
  (proof
   (
    (apply-macete-with-minor-premises tr%tr+accessible%from)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("next(s_0,a)" "a"))
    simplify))
  (theory det-hoare-machines)
  (usages transportable-macete))


(def-theorem det-state%histories-extensible-1
  state%histories-extensible-1
  (translation hoare-machines-to-det-hoare-machines)
  (theory det-hoare-machines)
  (proof existing-theorem)
  (usages transportable-macete))

(def-theory-ensemble det-hoare-machines)


 
