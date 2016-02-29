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


(herald LCT-OBLIGATIONS)


(def-theorem LCT-OBLIGATION-1
  "#(restrict2{mul,b,b},[b%sort,b%sort,b%sort])"
  lemma
  (theory lct-theory)
  (proof
   (
    sort-definedness
    simplify
    (apply-macete-with-minor-premises b%sort-defining-axiom_lct-theory)
    (apply-macete-with-minor-premises lct-macete)
    )))

(def-theorem LCT-OBLIGATION-2
  "#(restrict{inv,b},[b%sort,b%sort])"
  lemma
  (theory lct-theory)
  (proof
   (
    sort-definedness
    simplify
    (apply-macete-with-minor-premises b%sort-defining-axiom_lct-theory)
    (apply-macete-with-minor-premises lct-macete)
    )))

(def-theorem LCT-OBLIGATION-3
  "#(restrict2{right%trans,a%cosets,b},[a%cosets%sort,b%sort,a%cosets%sort])"
  lemma
  (theory lct-theory)
  (proof
   (
    sort-definedness
    direct-inference
    (case-split ("#(xx_0,sets[gg])"))
    simplify
    (unfold-single-defined-constant-globally a%cosets)
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises a%cosets%sort-defining-axiom_lct-theory)
    simplify
    (unfold-single-defined-constant-globally a%cosets)
    simplify
    (backchain "with(g:gg,xx_0:sets[gg],xx_0=right%trans(a,g))")
    (instantiate-existential ("g mul xx_1"))
    (apply-macete-with-minor-premises lct-macete)
    (apply-macete-with-minor-premises simplify-set-translations)
    simplify
    )))

(def-theorem LCT-OBLIGATION-4
  "forall(x:b%sort,inv(x) in b)"
  lemma
  (theory lct-theory)
  (proof
   (
    (apply-macete-with-minor-premises lct-macete)
    )))

(def-theorem LCT-OBLIGATION-5
  "forall(x,y:b%sort,(x mul y) in b)"
  lemma
  (theory lct-theory)
  (proof
   (
    (apply-macete-with-minor-premises lct-macete)
    )))

(def-theorem LCT-OBLIGATION-6
  "forall(g,h:b%sort,(g mul h) in b)
    and 
   (forall(alpha:a%cosets%sort,g:b%sort, right%trans(alpha,g) in a%cosets)
     and 
    forall(alpha:a%cosets%sort,g,h:b%sort,
     right%trans(alpha,g mul h)=right%trans(right%trans(alpha,g),h)))"
  lemma
  (theory lct-theory)
  (proof
   (
    (apply-macete-with-minor-premises lct-macete)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0 0)")
     (unfold-single-defined-constant-globally a%cosets)
     simplify
     (cut-with-single-formula "alpha in a%cosets")
     (block 
      (script-comment "node added by `cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(p:prop,p);")
      (unfold-single-defined-constant-globally a%cosets)
      simplify
      direct-and-antecedent-inference-strategy
      (backchain "with(f:sets[gg],alpha:a%cosets%sort,alpha=f);")
      (instantiate-existential ("g_$0 mul g"))
      (block 
       (script-comment "node added by `instantiate-existential' at (0 0)")
       (apply-macete-with-minor-premises lct-macete)
       (apply-macete-with-minor-premises b%sort-members-are-in-b))
      (apply-macete-with-minor-premises simplify-set-translations))
     (apply-macete-with-minor-premises a%cosets%sort-members-are-in-a%cosets))
    (apply-macete-with-minor-premises simplify-set-translations)
    )))

(def-theorem LCT-OBLIGATION-6-PERMUTED
  "forall(h,g:b%sort,(g mul h) in b)
    and 
   (forall(g:b%sort,alpha:a%cosets%sort, right%trans(alpha,g) in a%cosets)
     and 
    forall(alpha:a%cosets%sort,g,h:b%sort,
     right%trans(alpha,g mul h)=right%trans(right%trans(alpha,g),h)))"
  lemma
  (theory lct-theory)
  (proof
   (
    (assume-theorem lct-obligation-6)
    direct-and-antecedent-inference-strategy
    simplify
    )))

