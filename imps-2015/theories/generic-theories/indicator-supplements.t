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

(herald INDICATOR-SUPPLEMENTS)

(load-section foundation)

(def-constant max%on%set
  "lambda(s:sets[ind_1],f:[ind_1,rr],
     iota(r:rr, 
       forsome(x:ind_1, x in s and r = f(x))
        and
       forall(x:ind_1, x in s implies (not(#(f(x))) or f(x) <= r))))"
  (theory generic-theory-1))

(def-theorem max%on%set-bigger-than-members
  "forall(s:sets[ind_1],f:[ind_1,rr],x:ind_1,
     x in s 
      and
     #(f(x))
      and
     #(max%on%set(s,f))
      implies 
     f(x) <= max%on%set(s,f))"
  (theory generic-theory-1)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (incorporate-antecedent 
     "with(f:[ind_1,rr],s:sets[ind_1],#(max%on%set(s,f)));")
    (unfold-single-defined-constant-globally max%on%set)
    direct-inference
    (eliminate-defined-iota-expression 0 w)
    (backchain "with(p:prop,p and p);")
    direct-inference

    )))

(def-theorem disj-commutativity
  "forall(a,b:sets[uu], a disj b iff b disj a)"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (

    insistent-direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(b,a:sets[uu],a disj b);" ("x"))
    (instantiate-universal-antecedent "with(a,b:sets[uu],b disj a);" ("x"))

    )))

(def-theorem union-disjointness-left
  "forall(a,b,c:sets[uu], 
     (a union b) disj c 
      iff
     (a disj c and b disj c))"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (

    direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment 
       "`direct-and-antecedent-inference-strategy' at (0 0)")
      insistent-direct-inference
      (instantiate-universal-antecedent "with(p:prop,p);" ("x"))
      simplify
      simplify)
    (block 
      (script-comment 
       "`direct-and-antecedent-inference-strategy' at (0 1)")
      insistent-direct-inference
      (instantiate-universal-antecedent 
       "with(p:prop,forall(x_$0:uu,p and p or not(p)));"
       ("x"))
      simplify
      simplify)
    (instantiate-universal-antecedent 
     "with(c,a:sets[uu],a disj c);" ("x_$0"))
    (instantiate-universal-antecedent 
     "with(c,b:sets[uu],b disj c);" ("x_$0"))

    )))

(def-theorem union-disjointness-right
  "forall(a,b,c:sets[uu], 
     a disj (b union c) 
      iff
     (a disj b and a disj c))"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (

    (force-substitution "a disj b union c" "(b union c) disj a" (0))
    (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises union-disjointness-left)
      (apply-macete-locally 
       disj-commutativity (0) "(b disj a and c disj a)"))
    (block 
      (script-comment "`force-substitution' at (1)")
      (move-to-ancestor 1)
      (apply-macete-locally 
       disj-commutativity (0) "a disj b union c"))

    )))
