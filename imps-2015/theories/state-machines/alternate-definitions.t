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
;% COPYRIGHT NOTICE INSERTED: Wed Sep  7 09:05:33 EDT 1994

(herald alternate-definitions)

(def-constant alt%failure_q
  "lambda(f:[uu, sets[sets[action]]], 
     forall(u:uu,x,y:sets[action], y in f(u) and x subseteq y implies x in f(u))
     and
     e in support(f)
     and
    forall(u,v:uu, u in support(f) and v prefix u implies v in support(f))
     and
    forall(u:uu, a:action, x:sets[action],
        x in f(u) and 
        forall(m:uu, germ(m)=a implies not (u**m) in support(f))
         implies
         (x union singleton{a}) in f(u))
     and
    total_q{f,[uu ->  sets[sets[action]]]}
     and
    forall(u:uu,s:sets[action], s in f(u) implies not (germ(e)) in s))"
  (theory directed-monoid-theory))


(def-theorem failure-alt-failure-equivalence
  "forall(f:[uu, sets[sets[action]]], failure_q(f) iff alt%failure_q(f))"
  (theory monoid-transition-system)
  (proof
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 0 0)")
      (backchain "with(p:prop,forall(u:uu,x,y:sets[action],p));")
      auto-instantiate-existential)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 2 0 0 0 0)")
      (backchain "with(p:prop,forall(u,v:uu,p));")
      auto-instantiate-existential)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 3 0 0 0 0)")
      (backchain "with(p:prop,forall(u:uu,a:action,p));")
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(unfold-single-defined-constant (0) support)
	simplify-insistently
	auto-instantiate-existential)
      (backchain "with(p:prop,forall(m:uu,p implies p));"))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 5 0 0 0)")
      (backchain "with(p:prop,forall(u:uu,x,y:sets[action],p));")
      (backchain "with(p:prop,forall(u:uu,s:sets[action],p));")
      auto-instantiate-existential)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0 0 0 0)")
      (backchain "with(p:prop,forall(u:uu,x,y:sets[action],p));")
      auto-instantiate-existential)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 2 0 0 0 0)")
      (backchain "with(p:prop,forall(u,v:uu,p));")
      auto-instantiate-existential)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 3 0 0 0 0 0 0)")
      (backchain "with(p:prop,forall(u:uu,a:action,x:sets[action],p));")
      direct-and-antecedent-inference-strategy
      (backchain "with(p:prop,forall(m:uu,p or p));"))

    )))