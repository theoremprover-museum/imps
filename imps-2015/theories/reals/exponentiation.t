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


(herald exponentiation)

(load-section knaster-fixed-point-theorem)

;;some useful lemmas:

(def-theorem weak-positivity-for-r^n
  "forall(x:rr, n:zz, 1<=n and 0<=x implies 0<=x^n)"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (case-split ("x=0"))
    simplify
    (cut-with-single-formula "0<x^n")
    simplify
    (apply-macete-with-minor-premises positivity-for-r^n)
    simplify
    direct-and-antecedent-inference-strategy

    )))

(def-theorem positive-rational-characterization
  "forall(s:qq, 0<s implies forsome(m,n:zz, 1<=m and 1<=n and s=m/n))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(m,n:zz, s=m/n)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises zz-quotient-field)
    (antecedent-inference "with(p:prop,forsome(m,n:zz,p));")
    (cut-with-single-formula "0=m or 0<m or m<0")
    (move-to-sibling 1)
    simplify
    (antecedent-inference "with(p:prop,p or p or p);")
    (simplify-antecedent "with(n,m:zz,s:qq,s=m/n);")
    (instantiate-existential ("m" "n"))
    simplify
    (contrapose "with(r:rr,s:qq,s=r);")
    (cut-with-single-formula "n<0 or n=0")
    (antecedent-inference "with(p:prop,p or p);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    (cut-with-single-formula "0<(-s)*n")
    simplify
    simplify
    simplify
    simplify
    (instantiate-existential ("-m" "-n"))
    (incorporate-antecedent "with(r:rr,s:qq,s=r);")
    simplify
    (contrapose "with(r:rr,s:qq,s=r);")
    (cut-with-single-formula "n=0 or 0<n")
    (move-to-sibling 1)
    simplify
    (antecedent-inference "with(p:prop,p or p);")
    simplify
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    (cut-with-single-formula "0<s*n")
    simplify
    simplify
    (incorporate-antecedent "with(r:rr,s:qq,s=r);")
    simplify
    )))

(def-theorem rational-power-lemma-1
  "forall(x:rr, m,n,p:zz, 1<=n and 1<=m and 1<=p and 0<=x 
                           implies
                         nth%root(p*n,x^(p*m))= nth%root(n,x^m))"

  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises iota-free-characterization-of-nth%root)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises nth%root-non-negative)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s:rr, nth%root(n,x^m)=s)")
    (antecedent-inference "with(p:prop,forsome(s:rr,p));")
    (backchain "with(s,r:rr,r=s);")
    (incorporate-antecedent "with(s,r:rr,r=s);")
    (apply-macete-with-minor-premises iota-free-characterization-of-nth%root)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "(s^n)^p=(x^m)^p")
    (move-to-sibling 1)
    (backchain "with(r:rr,r=r);")
    simplify
    simplify
    (instantiate-existential ("nth%root(n,x^m)"))
    (force-substitution "1" "1*1" (0))
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    simplify

    )))

(def-theorem rational-power-lemma-2
  "forall(x:rr, m,n,p,q:zz, 1<=n and 1<=m and 1<=p and 1<=q and 0<=x and m/n=p/q
                implies
               nth%root(n,x^m)=nth%root(q,x^p))"

  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "nth%root(n,x^m)=nth%root(q*n,x^(q*m)) and nth%root(n*q,x^(n*p))=nth%root(q,x^p)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises rational-power-lemma-1)
    simplify
    (apply-macete-with-minor-premises nth%root%existence)
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,p and p);")
    (antecedent-inference "with(p:prop,p and p);")

    (force-substitution "q*m" "n*p" (0))
    (move-to-sibling 1)
    simplify
    (force-substitution "q*n" "n*q" (0))
    simplify)))

(def-theorem rational-power-lemma-3
  "forall(x:rr, m,n,p:zz, 1<=n and 1<=m and 0<=x 
                           implies
                         nth%root(n,x^m)= nth%root(n,x)^m)"

  (theory h-o-real-arithmetic)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises iota-free-characterization-of-nth%root)
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises nth%root-non-negative)
    simplify
    (force-substitution "(nth%root(n,x)^m)^n" "(nth%root(n,x)^n)^m" (0))
    (apply-macete-with-minor-premises nth%root-power)
    simplify
    simplify
    )))


(def-constant posrat%exp
  "lambda(x:rr, s:qq, 
       if(s<=0 or x<0,?rr,
         iota(r:rr, forall(m,n:zz,1<=m and 1<=n and s=m/n implies r=nth%root(n,x^m)))))"
  (theory h-o-real-arithmetic))

(def-theorem posrat%exp-characterization
  "forall(x:rr, m,n:zz,1<=m and 1<=n and 0<=x implies posrat%exp(x,m/n)=nth%root(n,x^m))"
  (theory h-o-real-arithmetic)
  (proof
   (

    
    (unfold-single-defined-constant (0) posrat%exp)
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (contrapose "with(r:rr,r<=0);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (simplify-antecedent "with(x:rr,x<0);")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises rational-power-lemma-2)
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises nth%root%existence)
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    direct-and-antecedent-inference-strategy
    
    )))



(def-theorem posrat%exp-definedness
  "forall(x:rr, s:qq,0<s and 0<=x implies #(posrat%exp(x,s)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(m,n:zz, s=m/n and 1<=m and 1<=n)")
    (antecedent-inference "with(p:prop,forsome(m,n:zz,p));")
    (backchain "with(p:prop,p and p and p);")
    (apply-macete-with-minor-premises posrat%exp-characterization)
    (apply-macete-with-minor-premises nth%root%existence)
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    direct-and-antecedent-inference-strategy
    (instantiate-theorem positive-rational-characterization ("s"))
    auto-instantiate-existential
    )))

(def-theorem posrat%exp-nonnegative
  "forall(x:rr, s:qq, 0<s and 0<=x implies 0<=posrat%exp(x,s))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(m,n:zz, 1<=m and 1<=n and s=m/n) ")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises positive-rational-characterization)
    (antecedent-inference "with(p:prop,forsome(m,n:zz,p));")
    (backchain "with(p:prop,p and p and p);")
    (apply-macete-with-minor-premises posrat%exp-characterization)
    (apply-macete-with-minor-premises nth%root-non-negative)
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    simplify
    )))


(def-theorem posrat%exp-additive-property
  "forall(x:rr, s,t:qq,0<s and 0<t and 0<=x 
                     implies
                     posrat%exp(x,s+t)=posrat%exp(x,s)*posrat%exp(x,t))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forsome(m,n:zz, 1<=m and 1<=n and s=m/n) and forsome(m,n:zz, 1<=m and 1<=n and t=m/n)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises positive-rational-characterization)
    direct-and-antecedent-inference-strategy
    (antecedent-inference-strategy (0))
    (backchain-repeatedly ("with(n_$0,m_$0:zz,s:qq,s=m_$0/n_$0);"))
    (backchain-repeatedly ("with(n,m:zz,t:qq,t=m/n);"))
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    (apply-macete-with-minor-premises posrat%exp-characterization)
    (move-to-sibling 1)
    (force-substitution "1" "1*1" (0))
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    simplify
    (move-to-sibling 2)
    (cut-with-single-formula "1<=m_$0*n and 0<=n_$0*m")
    simplify
    (force-substitution "1" "1*1" (0))
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    (force-substitution "x^(n_$0*m+n*m_$0)" "x^(n_$0*m)*x^(n*m_$0)" (0))
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises nth-root-is-multiplicative)
    (force-substitution "n*n_$0" "n_$0*n" (0))
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises rational-power-lemma-1)
    simplify
    (apply-macete-with-minor-premises nth%root%existence)
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    simplify
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    simplify
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    simplify


    )))

(def-theorem posrat%exp-multiplicative-property
  "forall(x,y:rr, s,t:qq,0<s and 0<=x and 0<=y
                     implies
                     posrat%exp(x*y,s)=posrat%exp(x,s)*posrat%exp(y,s))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(m,n:zz, 1<=m and 1<=n and s=m/n) ")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises positive-rational-characterization)
    (antecedent-inference-strategy (0))
    (backchain-repeatedly ("with(n_$0,m_$0:zz,s:qq,s=m_$0/n_$0);"))
    (apply-macete-with-minor-premises posrat%exp-characterization)
    simplify
    (apply-macete-with-minor-premises nth-root-is-multiplicative)
    simplify
    (apply-macete-with-minor-premises nth%root%existence)
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    (apply-macete-with-minor-premises positivity-for-products)
    direct-and-antecedent-inference-strategy

    )))

(def-theorem posrat%exp-iterated-exponent-property
  "forall(x,y:rr, s,t:qq,0<s and 0<t and 0<=x
                     implies
                     posrat%exp(x,s*t)=posrat%exp(posrat%exp(x,s),t))"
  (theory h-o-real-arithmetic)
  (proof
   (



    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forsome(m,n:zz, 1<=m and 1<=n and s=m/n) and forsome(m,n:zz, 1<=m and 1<=n and t=m/n)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises positive-rational-characterization)
    direct-and-antecedent-inference-strategy
    (antecedent-inference-strategy (0))
    (backchain-repeatedly ("with(n_$0,m_$0:zz,s:qq,s=m_$0/n_$0);"))
    (backchain-repeatedly ("with(n,m:zz,t:qq,t=m/n);"))
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    (apply-macete-with-minor-premises posrat%exp-characterization)
    (move-to-sibling 1)
    (apply-macete-with-minor-premises posrat%exp-nonnegative)
    direct-and-antecedent-inference-strategy
    (move-to-sibling 2)
    (force-substitution "1" "1*1" (0))
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    simplify
    (apply-macete-with-minor-premises posrat%exp-characterization)
    (apply-macete-with-minor-premises iterated-nth%root)
    (move-to-sibling 1)
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    (force-substitution "1" "1*1" (0))
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    (apply-macete-with-minor-premises rational-power-lemma-3)
    (move-to-sibling 1)
    (apply-macete-with-minor-premises nth%root-non-negative)
    (apply-macete-with-minor-premises weak-positivity-for-r^n)
    simplify
    (apply-macete-with-minor-premises rational-power-lemma-3)
    (move-to-sibling 1)
    (apply-macete-with-minor-premises nth%root-non-negative)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises rational-power-lemma-3)
    simplify
    (force-substitution "1" "1*1" (0))
    )))

(comment
 (def-constant rat%exp
  "lambda(x:rr, s:qq, if(0<s, posrat%exp(x,s),s=0,1,1/posrat%exp(x,-s)))"
  (theory h-o-real-arithmetic))


 (def-theorem rat%exp-additivity
  "forall(s,t:qq, x:rr, 0<=x 
                   implies
                  rat%exp(x,s+t)=rat%exp(x,s)*rat%exp(x,t))"
  (theory h-o-real-arithmetic)
  (proof
   (


    )))
)
