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


(herald recursive-formulas)

(include-files
 (files (imps theories/algebra/fields-supplements)
	(imps theories/reals/comb-ident)))


(def-recursive-constant comb_kk
  "lambda(rec:[zz,zz,kk], a,b:kk,
      lambda(m,k:zz, if(m<0, o_kk, m=0 and k=0, i_kk, 
               a*rec(m-1,k-1)+b*rec(m-1,k))))"
  (definition-name comb_kk)
  (theory fields))

(def-theorem comb_kk-null-lemma
  "forall(a,b:kk, m,k:zz, m<k implies comb_kk(a,b)(m,k)=o_kk)"
  lemma
  (theory fields)
  (proof
   (

    direct-inference
    (cut-with-single-formula
     "forall(m:zz,forall(k:zz,m<k implies comb_kk(a,b)(m,k)=o_kk))")
    (backchain "with(p:prop, forall(m:zz, p))")
    direct-inference
    (case-split ("0<=m"))
    (induction trivial-integer-inductor ())
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) comb_kk)
    simplify
    (unfold-single-defined-constant (0 1) comb_kk)
    simplify
    (backchain "with(p:prop, forall(k:zz,p))")
    simplify
    (unfold-single-defined-constant (0) comb_kk)
    simplify

    )))

(def-theorem comb_kk-second-null-lemma
  "forall(a,b:kk, m,k:zz, k<0 implies comb_kk(a,b)(m,k)=o_kk)"
  lemma
  (theory fields)
  (proof
   (
    direct-inference
    (cut-with-single-formula "forall(m:zz,forall(k:zz,k<0 implies comb_kk(a,b)(m,k)=o_kk))")
    (backchain "with(p:prop, forall(m:zz, p))")
    direct-inference
    (case-split ("0<=m"))
    (induction trivial-integer-inductor ())
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) comb_kk)
    (unfold-single-defined-constant (0 1) comb_kk)
    simplify
    (backchain-repeatedly ("with(p:prop, forall(k:zz, p))"))
    simplify
    (unfold-single-defined-constant (0) comb_kk)
    simplify


    )))

(def-theorem comb_kk-0-value-lemma
  "forall(a,b:kk,m:zz, not(b=o_kk) and 0<=m implies comb_kk(a,b)(m,0)=b^m)"
  lemma
  (theory fields)
  (proof
   (
    (induction trivial-integer-inductor ("m"))
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) comb_kk)
    simplify
    (apply-macete-with-minor-premises comb_kk-second-null-lemma)
    simplify

    )))

;;In the following, the inductive cut formula prevents definition expansion.
;;One could also use an inductor with a dont-unfold keyword

(def-theorem comb_kk-m-value-lemma
  "forall(a,b:kk,m:zz, not(a=o_kk) and 0<=m implies comb_kk(a,b)(m,m)=a^m)"
  lemma
  (theory fields)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forall(m:zz,0<=m implies forall(k:zz,0<=k and k<=m implies comb_kk(a,b)(k,k)=a^k))")
    (backchain "with(p:prop, forall(m:zz, p))")
    auto-instantiate-existential
    simplify
    (weaken (0))
    (induction trivial-integer-inductor ())
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) comb_kk)
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "k=0")
    simplify
    simplify
    (case-split ("k=1+t"))
    (unfold-single-defined-constant (0) comb_kk)
    simplify
    (backchain "with(b,a:kk,t:zz,
  forall(k:zz,0<=k and k<=t implies comb_kk(a,b)(k,k)=a^k));")
    (apply-macete-with-minor-premises comb_kk-null-lemma)
    simplify
    (backchain "with(b,a:kk,t:zz,
  forall(k:zz,0<=k and k<=t implies comb_kk(a,b)(k,k)=a^k));")
    simplify

    )))

(def-theorem comb_kk-ident
  "forall(a,b:kk,k,m:zz,
     not(k=0 and m=[-1])
      implies 
     comb_kk(a,b)(1+m,k)
     ==a*comb_kk(a,b)(m,k-1)+b*comb_kk(a,b)(m,k))"
  lemma
  (theory fields)
  (proof
   (
    (unfold-single-defined-constant (0) comb_kk)
    direct-and-antecedent-inference-strategy
    (case-split ("0<=m"))
    simplify
    (case-split ("m<[-1]"))
    simplify
    (unfold-single-defined-constant (0 1) comb_kk)
    simplify
    (cut-with-single-formula "m=[-1] and not(k=0)")
    simplify
    direct-inference
    simplify
    (contrapose "with(m,k:zz,not(k=0 and m=[-1]));")
    direct-and-antecedent-inference-strategy

    )))

(def-compound-macete comb_kk-values
  (repeat
   comb-0-value-lemma
   comb-m-value-lemma
   comb_kk-m-value-lemma
   comb_kk-0-value-lemma
   comb-ident
   comb_kk-ident))

;;The proof of the following is almost identical to the proof of the integrality of
;;comb. The structure of the induction is similar.

(def-theorem comb-is-a-comb_kk
  "forall(m,k:zz, a,b:kk,  not(a=o_kk) and not(b=o_kk) and 0<=k and k<=m implies
          comb(m,k)*a^k*b^(m-k)
          =comb_kk(a,b)(m,k))"
  (proof
   (
    (cut-with-single-formula
     "forall(m:zz,0<=m implies
         forall(k,p:zz,a,b:kk,not(a=o_kk) and not(b=o_kk) and 0<=k and k<=p and p<=m 
             implies comb(p,k)*a^k*b^(p-k)=comb_kk(a,b)(p,k)))")
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop, forall(m:zz,  0<=m implies p))")
    (instantiate-existential ("m"))
    simplify
    simplify
    (induction trivial-integer-inductor ())
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "k=0 and p=0")
    simplify
    (apply-macete-with-minor-premises comb_kk-values)
    simplify
    simplify
    (case-split ("p<=t"))
    (backchain "with(r:prop, forall(k,p:zz,a,b:kk, r))")
    direct-and-antecedent-inference-strategy
    (case-split ("k=0"))
    (backchain-repeatedly ("with(k:zz,k=0);"))
    (apply-macete-with-minor-premises comb_kk-values)
    simplify
    (case-split ("k=p"))
    (backchain-repeatedly ("with(p,k:zz,k=p);"))
    (apply-macete-with-minor-premises comb_kk-values)
    simplify
    (force-substitution "p" "1+t" (0 1 2))
    (apply-macete-with-minor-premises comb_kk-values)
    (backchain-backwards "with(r:prop, forall(k,p:zz,a,b:kk, r))")
    (backchain-backwards "with(r:prop, forall(k,p:zz,a,b:kk, r))")
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify
    (weaken (2 4 6 7 8 12))
    (apply-macete-with-minor-premises external-multiplication-conversion)
    simplify
    simplify

    ))
  (theory fields))

(def-theorem com_kk-definedness
  "forall(a,b:kk,m,k:zz, #(comb_kk(a,b)(m,k)))"
  (theory fields)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("m<0"))
    (unfold-single-defined-constant (0) comb_kk)
    simplify
    (cut-with-single-formula
     "forall(m:zz, 0<=m implies forall(p,k:zz, 0<=p and p<=m implies #(comb_kk(a,b)(p,k))))")
    (backchain "with(p:prop, forall(m:zz, p))")
    (instantiate-existential ("m"))
    simplify
    simplify
    (weaken (0))
    (induction trivial-integer-inductor ())
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(comb_kk(a,b)(0,k))")
    (cut-with-single-formula "p=0")
    simplify
    simplify
    (unfold-single-defined-constant (0) comb_kk)
    (unfold-single-defined-constant (0 1) comb_kk)
    simplify
    (case-split ("p<=t"))
    (backchain "with(r:prop, forall(p:zz, r))")
    direct-and-antecedent-inference-strategy
    (force-substitution "p" "1+t" (0))
    (apply-macete-with-minor-premises comb_kk-ident)
    simplify
    direct-and-antecedent-inference-strategy
    (backchain "with(r:prop, forall(p:zz, r))")
    simplify
    (backchain "with(r:prop, forall(p:zz, r))")
    simplify

    )))
			       

(def-constant diffuse
  "lambda(a,b:kk, lambda(rho:[zz,kk], lambda(j:zz, a*rho(j)+b*rho(j-1))))"
  (theory fields))


(def-theorem diffuse_comb
  "forall(m:zz,a,b:kk,
     0<=m
      implies 
     diffuse(a,b)(lambda(j:zz,comb_kk(b,a)(m,j)))
     =lambda(j:zz,comb_kk(b,a)(1+m,j)))"
  (theory fields)
  (proof
   (

    (unfold-single-defined-constant (0) diffuse)
    direct-and-antecedent-inference-strategy
    extensionality
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises comb_kk-ident)
    simplify



    )))


(def-theorem expansion-lemma
  "forall(a,b:kk,m,n,p:zz,rho:[zz,kk],
     total_q{rho,[zz,kk]} and m-1<=n
      implies 
     sum(m,n,rho)*(a+b)
     =sum(m,n+1,diffuse(a,b)(rho))-a*rho(n+1)- b*rho(m-1))"
  (theory fields)
  (proof
   (
    (unfold-single-defined-constant (0) diffuse)
    (apply-macete tr%monoid-prod-out)
    (induction trivial-integer-inductor ())
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%monoid-null-prod)
    simplify


    )))

(def-theorem binomial-expansion-lemma
  "forall(a,b:kk,m,n,p:zz, 1<=n and 0<=m
      implies 
     sum(0,m,lambda(j:zz,comb_kk(b,a)(m,j)))*(a+b)^n=
     sum(0,m+n,lambda(j:zz,comb_kk(b,a)(m+n,j))))"
  (theory fields)
  lemma
  (proof
   (

    (induction trivial-integer-inductor ("n"))
    (block 
      (script-comment "`induction' at (0 0 0 0 0 0 0)") beta-reduce-repeatedly
      (force-substitution "(a+b)^1" "a+b" (0))
      (block 
	(script-comment "`force-substitution' at (0)")
	(apply-macete-with-minor-premises expansion-lemma)
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (0)")
	  beta-reduce-repeatedly (apply-macete comb_kk-null-lemma)
	  (apply-macete comb_kk-second-null-lemma)
	  (apply-macete-with-minor-premises diffuse_comb) simplify
	  (apply-macete-with-minor-premises sum_kk-definedness)
	  direct-and-antecedent-inference-strategy beta-reduce-repeatedly
	  (apply-macete-with-minor-premises com_kk-definedness)
	  )
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)")
	  insistent-direct-inference beta-reduce-repeatedly
	  (apply-macete-with-minor-premises com_kk-definedness)
	  ) )
      simplify
      )
    (block 
      (script-comment "`induction' at (0 0 0 0 0 0 1 0 0 0 0)")
      (force-substitution "sum(0,m,lambda(j:zz,comb_kk(b,a)(m,j)))*(b+a)^(1+t)"
			  "sum(0,m,lambda(j:zz,comb_kk(b,a)(m,j)))*(b+a)^t*(a+b)" (0)
			  )
      (block 
	(script-comment "`force-substitution' at (0)")
	(backchain "with(k:kk,k=k);")
	(apply-macete-with-minor-premises expansion-lemma)
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (0)")
	  beta-reduce-repeatedly (apply-macete comb_kk-null-lemma)
	  (apply-macete comb_kk-second-null-lemma)
	  (apply-macete-with-minor-premises diffuse_comb) simplify
	  (apply-macete-with-minor-premises sum_kk-definedness)
	  beta-reduce-repeatedly
	  (apply-macete-with-minor-premises com_kk-definedness)
	  )
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)")
	  insistent-direct-inference beta-reduce-repeatedly
	  (apply-macete-with-minor-premises com_kk-definedness)
	  ) )
      simplify
      )


    )))

(make-tex-correspondence "kk" "\{ \\bf K \}")

(def-theorem binomial-theorem
  "forall(a,b:kk, n:zz, 1<=n and not(a=o_kk) and not(b=o_kk) implies
            (a+b)^n=sum(0,n,lambda(j:zz,comb(n,j)*b^j*a^(n-j))))"
  (theory fields)
  (usages transportable-macete)
  (proof
   (
    (force-substitution "(a+b)^n" "sum(0,0,lambda(j:zz,comb_kk(b,a)(0,j)))*(a+b)^n" (0))
    (apply-macete-with-minor-premises binomial-expansion-lemma)
    (apply-macete-with-minor-premises tr%local-context-introduction-for-monoid-prod)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises comb-is-a-comb_kk)
    simplify
    (apply-macete-with-minor-premises sum_kk-definedness)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises com_kk-definedness)
    (apply-macete-with-minor-premises tr%monoid-triv-prod)
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) comb_kk)
    simplify

    )))

