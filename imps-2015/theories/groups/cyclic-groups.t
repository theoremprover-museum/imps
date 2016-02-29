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


(herald cyclic-groups)

(include-files 
  (files (imps theories/groups/groups)))


(def-theory abelian-groups
  (component-theories groups)
  (axioms
    (group-commutativity "forall(x,y:gg, x mul y = y mul x)")))

(def-recursive-constant multiple
  "lambda(phi:[zz,gg,gg], 
     lambda(k:zz, m:gg,if(0<k,m mul phi(k-1,m),k=0, e, inv(phi(-k,m)))))"
  (definition-name multiple)
  (theory abelian-groups))

(def-overloading + (h-o-real-arithmetic +) (abelian-groups mul))
(def-overloading - (h-o-real-arithmetic -) (abelian-groups inv))

;; (!)

(def-theorem multiple-totality
  "total_q{multiple,[zz,gg,gg]}"
  (theory abelian-groups)
  (usages d-r-convergence transportable-macete)
  (proof
   (

    insistent-direct-inference
    (case-split ("0<=x_0"))
    (induction integer-inductor ("x_0"))
    (unfold-single-defined-constant (0) multiple)
    simplify
    (cut-with-single-formula "forall(n:zz,0<=n implies #(multiple(n,x_1)))")
    (backchain "with(x_1:gg,forall(n:zz,0<=n implies #(multiple(n,x_1))));")
    simplify
    (weaken (0))

    )))

(def-theorem multiple-additivity-lemma
  "forall(m,n:zz, g:gg, 0<=m and 0<=n implies multiple(m+n,g)=multiple(m,g)+multiple(n,g))"
  reverse
  lemma
  (proof
   (
    (induction trivial-integer-inductor ())
    beta-reduce-repeatedly
    (unfold-single-defined-constant (1) multiple)
    simplify
    (unfold-single-defined-constant (0) multiple)
    simplify


    ))
  (theory abelian-groups))

(def-theorem multiple-difference-lemma
  "forall(m,n:zz, g:gg, 0<=m and 0<=n implies multiple(m-n,g)=multiple(m,g)+-multiple(n,g))"
  lemma
  (proof
   (

    direct-and-antecedent-inference-strategy
    (case-split ("n<=m"))
    (block 
      (script-comment "`case-split' at (1)")
      (cut-with-single-formula " multiple(m,g)=multiple(m-n,g)+multiple(n,g)")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(backchain "with(g:gg,g=g);")
	(apply-macete-with-minor-premises group-cancellation-laws)
	(apply-macete-with-minor-premises right-mul-inv)
	)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises rev%multiple-additivity-lemma) simplify
	) )
    (block 
      (script-comment "`case-split' at (2)")
      (force-substitution "m-n" "-(n-m)" (0))
      (block 
	(script-comment "`force-substitution' at (0)")
	(unfold-single-defined-constant (0) multiple) simplify
	(cut-with-single-formula "multiple(n,g)=multiple(n+[-1]*m,g)+multiple(m,g)"
				 )
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (backchain "with(g:gg,g=g);") (apply-macete-with-minor-premises push-inv)
	  (apply-macete-with-minor-premises group-cancellation-laws)
	  (apply-macete-with-minor-premises right-mul-inv)
	  )
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (apply-macete-with-minor-premises rev%multiple-additivity-lemma) simplify
	  ) )
      simplify
      )

    ))
  (theory abelian-groups))

(def-theorem multiple-is-additive
  "forall(m,n:zz, g:gg, multiple(m+n,g)=multiple(m,g)+multiple(n,g))"
  (proof
   (
    direct-inference
    (case-split ("0<=n" "0<=m"))
    (apply-macete-with-minor-premises rev%multiple-additivity-lemma)
    (force-substitution "m+n" "n-(-m)" (0))
    (apply-macete-with-minor-premises multiple-difference-lemma)
    (unfold-single-defined-constant (2) multiple)
    simplify
    (assume-theorem group-commutativity)
    (backchain "forall(x,y:gg,x+y=y+x);")
    simplify
    (force-substitution "m+n" "m-(-n)" (0))
    (apply-macete-with-minor-premises multiple-difference-lemma)
    (apply-macete-with-minor-premises group-cancellation-laws)
    (unfold-single-defined-constant (1) multiple)
    simplify
    simplify
    (unfold-single-defined-constant (0 1 2) multiple)
    simplify
    (apply-macete-with-minor-premises multiple-additivity-lemma)
    (apply-macete-with-minor-premises push-inv)
    (assume-theorem group-commutativity)
    (backchain "forall(x,y:gg,x+y=y+x);")

    ))
  (theory abelian-groups)
  (usages transportable-macete))

(def-theorem multiple-is-additive-in-group
  "forall(m:zz, g,h:gg, multiple(m,g+h)=multiple(m,g)+multiple(m,h))"
  (theory abelian-groups)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    (case-split ("0<=m"))
    (induction trivial-integer-inductor ("m"))
    beta-reduce-repeatedly
    unfold-defined-constants
    simplify
    (apply-macete-with-minor-premises group-cancellation-laws)
    (assume-theorem group-commutativity)
    (backchain "forall(x,y:gg,x+y=y+x);")
    unfold-defined-constants
    simplify
    (cut-with-single-formula
     "forall(m:zz,0<=m implies multiple(m,g+h)=multiple(m,g)+multiple(m,h))")
    (backchain "with(h,g:gg,
  forall(m:zz,
    0<=m implies 
    multiple(m,g+h)=multiple(m,g)+multiple(m,h)));")
    (apply-macete-with-minor-premises push-inv)
    (assume-theorem group-commutativity)
    (backchain "forall(x,y:gg,x+y=y+x);")
    direct-and-antecedent-inference-strategy
    simplify

    )))

(def-theorem multiple-commutes-with-negation
  "forall(m:zz,g:gg, multiple([-1]*m,g)=-multiple(m,g))"
  (theory abelian-groups)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("0<=m"))
    (unfold-single-defined-constant (0) multiple)
    simplify
    (case-split ("0=m"))
    simplify
    (unfold-single-defined-constant (0) multiple)
    simplify
    simplify
    (unfold-single-defined-constant (1) multiple)
    simplify

    )))

(def-theorem multiple-commutes-with-negation-corollary
  "forall(g:gg, multiple([-1],g)=-g)"
  (theory abelian-groups)
  (proof
   (
    (force-substitution "[-1]" "[-1]*1" (0))
    (apply-macete-with-minor-premises multiple-commutes-with-negation)
    (unfold-single-defined-constant (0) multiple)
    simplify
    (unfold-single-defined-constant (0) multiple)
    simplify
    simplify

    )))

(def-theorem multiple-commutes-with-negation-in-group
  "forall(m:zz,g:gg, multiple(m,-g)=-multiple(m,g))"
  (theory abelian-groups)
  (proof
   (
    direct-inference
    (case-split ("0<=m"))
    (induction trivial-integer-inductor ("m"))
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0 1) multiple)
    simplify
    (assume-theorem group-commutativity)
    (backchain "forall(x,y:gg,x+y=y+x);")
    (unfold-single-defined-constant (0 1) multiple)
    simplify
    (cut-with-single-formula "forall(m:zz, 0<=m implies multiple(m,-g)=-multiple(m,g))")
    (backchain "with(g:gg,
  forall(m:zz,0<=m implies multiple(m,-g)=-multiple(m,g)));")
    direct-inference
    simplify

    )))

(def-theorem multiple-is-homogenuous
  "forall(m,n:zz, g:gg, multiple(m*n,g)=multiple(m,multiple(n,g)))"
  (theory abelian-groups)
  (proof
   (
    direct-inference
    (case-split ("0<=m"))
    (induction trivial-integer-inductor ())
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0 1) multiple)
    simplify
    (apply-macete-with-minor-premises multiple-is-additive)
    (force-substitution "m*n" "([-1]*m)*([-1]*n)" (0))
    (cut-with-single-formula "forall(m,n,k:zz,g:gg,0<=m implies
  multiple(m*n,g)=multiple(m,multiple(n,g)))")
    (backchain "forall(m,n,k:zz,g:gg,
  0<=m implies multiple(m*n,g)=multiple(m,multiple(n,g)));")
    direct-inference
    simplify
    (apply-macete-with-minor-premises multiple-commutes-with-negation)
    (apply-macete-with-minor-premises multiple-commutes-with-negation)
    (apply-macete-with-minor-premises multiple-commutes-with-negation-in-group)
    (apply-macete-with-minor-premises inv-of-inv)
    (weaken (0))
    direct-and-antecedent-inference-strategy
    simplify


    ))

  (usages transportable-macete))

(def-theorem multiple-of-group-identity
  "forall(m:zz, multiple(m,e)=e)"
  (theory abelian-groups)
  (proof
   (
    direct-inference
    (cut-with-single-formula "multiple(m,e)=multiple(m,e)+multiple(m,e)")
    (incorporate-antecedent "with(m:zz,multiple(m,e)=multiple(m,e)+multiple(m,e));")
    (apply-macete-with-minor-premises group-cancellation-laws)
    simplify
    (cut-with-single-formula "multiple(m,e)+multiple(m,e)=multiple(m,e+e)")
    (backchain "with(m:zz,multiple(m,e)+multiple(m,e)=multiple(m,e+e));")
    (apply-macete-with-minor-premises right-mul-id)
    (apply-macete-with-minor-premises multiple-is-additive-in-group)

    )))

(def-theorem 0-multiple-is-group-identity
  "forall(g:gg, multiple(0,g)=e)"
  (theory abelian-groups)
  (proof
   (
    (unfold-single-defined-constant (0) multiple)
    simplify
    )))

(def-theorem 1-multiple-is-element
  "forall(g:gg, multiple(1,g)=g)"
  (theory abelian-groups)
  (proof
   (
    (unfold-single-defined-constant (0) multiple)
    simplify
    (unfold-single-defined-constant (0) multiple)
    simplify

    )))

(def-theorem multiple-totality-with-range
  "forall(g:gg,n:zz, #(multiple(n,g),gg))"
  (theory abelian-groups)
  (proof
   (
    direct-inference
    )))
