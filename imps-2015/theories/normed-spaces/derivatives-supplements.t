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


(herald derivatives-supplements)

(include-files
 (files (imps theories/normed-spaces/derivatives)))

(def-language mappings-from-an-interval-to-ns-extension
  (embedded-languages mappings-from-an-interval-to-a-normed-space)
  (constants
   (a ii)
   (b ii)))
  
(def-theory mappings-from-an-interval-with-endpoints-to-a-normed-space
  (language mappings-from-an-interval-to-ns-extension)
  (component-theories mappings-from-an-interval-to-a-normed-space)
  (axioms
   (endpoint-ordering "a<b")))

;; obligations
;; This definition is "skewed" to the left, because our definition of derivative 
;; is skewed to the right.

(def-theorem ()
  "lambda(x:ii,a<=x and x<b)((a+b)/2)"
  (theory  mappings-from-an-interval-with-endpoints-to-a-normed-space)
  (proof
   (
    simplify
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("b" "a"))
    simplify
    simplify

    )))


(def-atomic-sort jj
  "lambda(x:ii, a<=x and x<b)"
  (theory  mappings-from-an-interval-with-endpoints-to-a-normed-space)
  (witness "(a+b)/2"))
  
(def-theorem ()
  "forall(x:rr,
     forsome(u:jj,u<=x) and forsome(v:jj,x<=v) implies #(x,jj))"
  lemma
  (theory mappings-from-an-interval-with-endpoints-to-a-normed-space)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(u,jj) and #(v,jj)")
    (incorporate-antecedent "with(v,u:jj,#(u,jj) and #(v,jj));")
    (apply-macete-with-minor-premises
     jj-defining-axiom_mappings-from-an-interval-with-endpoints-to-a-normed-space)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    beta-reduce-with-minor-premises
    simplify
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("b" "a"))
    simplify
    simplify


    )))


(def-theorem ()
  "forsome(x,y:jj,x<y)"
  (theory  mappings-from-an-interval-with-endpoints-to-a-normed-space)
  lemma
  (proof
   (

    (instantiate-existential ("1/3*b+2/3*a" "1/3*a+2/3*b"))
    simplify
    (apply-macete-with-minor-premises
     jj-defining-axiom_mappings-from-an-interval-with-endpoints-to-a-normed-space)
    simplify
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("b" "a"))
    simplify
    simplify
    (apply-macete-with-minor-premises
     jj-defining-axiom_mappings-from-an-interval-with-endpoints-to-a-normed-space)
    simplify
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("b" "a"))
    simplify
    simplify

    )))

(def-theory-ensemble-instances
  metric-spaces 
  force-under-quick-load
  (target-theories mappings-from-an-interval-with-endpoints-to-a-normed-space
		   mappings-from-an-interval-with-endpoints-to-a-normed-space)
  (permutations (0 1))
  (theory-interpretation-check using-simplification)
  (sorts (pp jj uu))
  (constants (dist "lambda(x,y:jj, abs(x-y))" "lambda(x,y:uu, norm(x-y))"))
  (special-renamings
   (uniformly%continuous uniformly%continuous%jj%uu)
   (continuous%at%point continuous%at%point%jj%uu)
   (lipschitz%bound lipschitz%bound%jj%uu)
   (lipschitz%bound%on lipschitz%bound%on%jj%uu)))
	     
(def-translation mappings-from-an-interval-to-ns-extension-specialization
  force-under-quick-load
  (source mappings-from-an-interval-to-a-normed-space)
  (target mappings-from-an-interval-with-endpoints-to-a-normed-space)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ii jj))
  (theory-interpretation-check using-simplification))

(def-renamer deriv-res-renamer
  (pairs
   (deriv deriv_r)))
 
(def-transported-symbols (deriv)
  (translation mappings-from-an-interval-to-ns-extension-specialization)
  (renamer deriv-res-renamer)
  )

(def-theorem deriv_r-restricts-deriv-lemma
  "forall(f:[jj,uu], x:jj, #(deriv(f,x)) implies deriv(f,x)=deriv_r(f,x))"
  (theory  mappings-from-an-interval-with-endpoints-to-a-normed-space)
  lemma
  reverse
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("forsome(v:uu,deriv(f,x)=v)"))
    (antecedent-inference "with(x:jj,f:[jj,uu],forsome(v:uu,deriv(f,x)=v));")
    (backchain "with(v:uu,x:jj,f:[jj,uu],deriv(f,x)=v);")
    (cut-with-single-formula "deriv_r(f,x)=v")
    (incorporate-antecedent "with(v:uu,x:jj,f:[jj,uu],deriv(f,x)=v);")
    (apply-macete-with-minor-premises characterization-of-derivative)
    (apply-macete-with-minor-premises tr%characterization-of-derivative)
    direct-and-antecedent-inference-strategy
    (auto-instantiate-universal-antecedent "with(p:prop,forall(eps:rr,0<eps implies p))")
    (cut-with-single-formula "forsome(u:jj, x<u and u<b and u<=z_0)")
    (antecedent-inference "with(z_0:ii,x:jj,forsome(u:jj,x<u and u<b and u<=z_0));")
    (instantiate-existential ("u"))
    (backchain "with(p:prop,   forall(z:ii,p))")
    simplify
    (instantiate-existential ("min((b+x)/2,z_0)"))
    (cut-with-single-formula "a<=x and x<b")
    (unfold-single-defined-constant (0) min)
    (case-split ("(b+x)/2<=z_0"))
    simplify
    simplify
    (cut-with-single-formula "#(x,jj)")
    (incorporate-antecedent "with(x:jj,#(x,jj));")
    (apply-macete-with-minor-premises 
     jj-defining-axiom_mappings-from-an-interval-with-endpoints-to-a-normed-space)
    simplify
    (cut-with-single-formula "x<b and min((b+x)/2,z_0)<=(b+x)/2")
    simplify
    (apply-macete-with-minor-premises minimum-1st-arg)
    (apply-macete-with-minor-premises minimum-2nd-arg)
    (apply-macete-with-minor-premises 
     jj-defining-axiom_mappings-from-an-interval-with-endpoints-to-a-normed-space)
    simplify
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("b" "a"))
    (unfold-single-defined-constant (0) min)
    (case-split ("[1/2]*b+[1/2]*x<=z_0"))
    simplify
    (cut-with-single-formula "#(x,jj)")
    (incorporate-antecedent "with(x:jj,#(x,jj));")
    (apply-macete-with-minor-premises 
     jj-defining-axiom_mappings-from-an-interval-with-endpoints-to-a-normed-space)

    beta-reduce-with-minor-premises
    direct-and-antecedent-inference-strategy
    simplify
    simplify


    )))

(def-theory-ensemble-overloadings metric-spaces (1 2))

(def-theorem constant-on-subintervals
  "forall(f:[jj,uu], 
     total_q{f,[jj,uu]} 
      and
     continuous(f)
      and
     forall(x:jj, deriv(f,x)=v0)
      implies
     forall(x,y:jj,f(x)=f(y)))"
  lemma
  (theory mappings-from-an-interval-with-endpoints-to-a-normed-space)
  (proof

   (

    (apply-macete-with-minor-premises tr%mean-value-theorem-corollary-0)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises rev%deriv_r-restricts-deriv-lemma)
    (backchain "with(f:[jj,uu],forall(x:jj,deriv(f,x)=v0));")


    )))

;;;The following theorem is installed in mappings-from-an-interval-to-a-normed-space.
;;;forall(b,a:ii,
;;;  a<b
;;;   implies 
;;;  forall(f:[ii,uu],
;;;    forall(x_0:ii,a<=x_0 and x_0<b implies #(f(x_0)))
;;;     and 
;;;    forall(x:ii,
;;;      a<=x and x<b implies continuous%at%point(f,x))
;;;     and 
;;;    forall(x:ii,a<=x and x<b implies deriv(f,x)=v0)
;;;     implies 
;;;    forall(x,y:ii,
;;;      (a<=x and x<b) and (a<=y and y<b) implies f(x)=f(y))))

(def-theorem constant-on-subintervals-corollary
  "forall(f:[ii,uu], 
     total_q{f,[jj,uu]} 
      and
     forall(x:jj,continuous%at%point(f,x))
      and
     forall(x:jj, deriv(f,x)=v0)
      implies
     forall(x,y:jj,f(x)=f(y)))"
  (home-theory mappings-from-an-interval-with-endpoints-to-a-normed-space)
  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof

   (

    direct-and-antecedent-inference-strategy
    (force-substitution "f(x)=f(y)" "lambda(z:jj,f(z))(x)=lambda(z:jj,f(z))(y)" (0))
    (apply-macete-with-minor-premises constant-on-subintervals)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    (weaken (0 1))
    (incorporate-antecedent "with(f:[ii,uu],forall(x:jj,continuous%at%point(f,x)));")
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop, forall(x:jj, forall(eps:rr,
      0<eps implies p)))" ("x_$0"))
    (auto-instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))")
    (instantiate-existential ("delta_$0"))
    (backchain "with(p,q:prop, forall(y_$0:ii, p implies q))")
    (cut-with-single-formula "deriv(lambda(z:jj,f(z)),x)==deriv(f,x)")
    (backchain "with(x:jj,f:[ii,uu],deriv(lambda(z:jj,f(z)),x)==deriv(f,x));")
    (backchain "with(f:[ii,uu],forall(x:jj,deriv(f,x)=v0));")
    (apply-macete-with-minor-premises locality-of-derivative)
    (cut-with-single-formula "forall(x:jj,a<=x and x<b)")
    (instantiate-existential ("b"))
    simplify
    beta-reduce-with-minor-premises
    simplify
    (instantiate-universal-antecedent "with(f:[ii,uu],total_q{f,[jj,uu]});" ("t"))
    (apply-macete-with-minor-premises
     jj-defining-axiom_mappings-from-an-interval-with-endpoints-to-a-normed-space)
    simplify
    (instantiate-universal-antecedent "forall(x:jj,a<=x and x<b);" ("x"))
    simplify
    (apply-macete-with-minor-premises
     jj-in-quasi-sort_mappings-from-an-interval-with-endpoints-to-a-normed-space)
    beta-reduce-with-minor-premises

    )))

(def-theorem mean-value-theorem-on-subintervals
  "forall(f:[jj,uu],m:rr,
     total_q{f,[jj,uu]}
      and 
     continuous(f)
      and 
     forall(x:jj,norm(deriv(f,x))<=m)
      implies 
     forall(x,y:jj,norm(f(x)-f(y))<=m*abs(x-y)))"
  lemma
  (theory mappings-from-an-interval-with-endpoints-to-a-normed-space)
  (proof

   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "m<0 or m=0 or 0<m")
    (antecedent-inference "with(m:rr,m<0 or m=0 or 0<m);")
    (contrapose "with(m:rr,f:[jj,uu],forall(x:jj,norm(deriv(f,x))<=m));")
    (instantiate-existential ("x"))
    (case-split ("#(deriv(f,x))"))
    (cut-with-single-formula "0<=norm(deriv(f,x))")
    simplify
    (apply-macete-with-minor-premises positivity-of-norm)
    simplify
    (cut-with-single-formula "f(x)=f(y)")
    simplify
    (apply-macete-with-minor-premises tr%mean-value-theorem-corollary-0)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises rev%deriv_r-restricts-deriv-lemma)
    (cut-with-single-formula "norm(deriv(f,x))=0")
    (incorporate-antecedent "norm(deriv(f,x))=0;")
    (apply-macete-with-minor-premises norm-zero)
    simplify
    (cut-with-single-formula "lipschitz%bound(f,m)")
    (incorporate-antecedent "with(m:rr,f:[jj,uu],lipschitz%bound(f,m));")
    (unfold-single-defined-constant (0) lipschitz%bound%jj%uu)
    (unfold-single-defined-constant (0) lipschitz%bound%on%jj%uu)
    direct-and-antecedent-inference-strategy
    (backchain "with(m:rr,f:[jj,uu],
  forall(x_$0,y_$0:jj,
    x_$0 in sort_to_indic{jj} and y_$0 in sort_to_indic{jj}
     implies 
    norm(f(x_$0)-f(y_$0))<=m*abs(x_$0-y_$0)));")
    simplify
    (apply-macete-with-minor-premises tr%mean-value-theorem)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises rev%deriv_r-restricts-deriv-lemma)
    (backchain "with(m:rr,f:[jj,uu],forall(x:jj,norm(deriv(f,x))<=m));")
    simplify

    )))

;;;forall(b,a:ii,
;;;  a<b
;;;   implies 
;;;  forall(f:[ii,uu],m:rr,
;;;    forall(x_0:ii,a<=x_0 and x_0<b implies #(f(x_0)))
;;;     and 
;;;    forall(x:ii,
;;;      a<=x and x<b implies continuous%at%point(f,x))
;;;     and 
;;;    forall(x:ii,a<=x and x<b implies norm(deriv(f,x))<=m)
;;;     implies 
;;;    forall(x,y:ii,
;;;      (a<=x and x<b) and (a<=y and y<b)
;;;       implies 
;;;      norm(f(x)-f(y))<=m*abs(x-y))))

(def-theorem mean-value-theorem-on-subintervals-corollary
  "forall(f:[ii,uu],m:rr,
     total_q{f,[jj,uu]}
      and 
     forall(x:jj,continuous%at%point(f,x))
      and 
     forall(x:jj,norm(deriv(f,x))<=m)
      implies 
     forall(x,y:jj,norm(f(x)-f(y))<=m*abs(x-y)))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (home-theory mappings-from-an-interval-with-endpoints-to-a-normed-space)
  (usages transportable-macete)
  (proof

   (
    
    direct-and-antecedent-inference-strategy
    (force-substitution "norm(f(x)-f(y))"
			"norm(lambda(z:jj,f(z))(x)-lambda(z:jj,f(z))(y))" (0))
    (apply-macete-with-minor-premises mean-value-theorem-on-subintervals)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(f:[ii,uu],forall(x:jj,continuous%at%point(f,x)));")
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop, forall(x:jj, forall(eps:rr,
      0<eps implies p)))" ("x_$0"))
    (auto-instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))")
    (instantiate-existential ("delta_$0"))
    (backchain "with(p,q:prop, forall(y_$0:ii, p implies q))")
    (cut-with-single-formula "forall(x:jj,deriv(lambda(z:jj,f(z)),x)==deriv(f,x))")
    (cut-with-single-formula "forall(x:jj,a<=x and x<b)")
    (backchain "with(f:[ii,uu],
  forall(x:jj,deriv(lambda(z:jj,f(z)),x)==deriv(f,x)));")
    (backchain "with(m:rr,f:[ii,uu],forall(x:jj,norm(deriv(f,x))<=m));")
    (apply-macete-with-minor-premises
     jj-in-quasi-sort_mappings-from-an-interval-with-endpoints-to-a-normed-space)
    (apply-macete-with-minor-premises locality-of-derivative)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("b"))
    (cut-with-single-formula "a<=x and x<b")
    (apply-macete-with-minor-premises
     jj-in-quasi-sort_mappings-from-an-interval-with-endpoints-to-a-normed-space)
    (cut-with-single-formula "#(t,jj)")
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises
     jj-defining-axiom_mappings-from-an-interval-with-endpoints-to-a-normed-space)
    (cut-with-single-formula "a<=x")
    beta-reduce-repeatedly
    simplify
    beta-reduce-repeatedly


    )))


;; These results have consequences in terms of integrals: The integral of a 
;; function which is v0 on the open interval [a,b) is zero there.
;; More generally, the integral is local.

(include-files
 (files (imps theories/normed-spaces/integrals)))

(def-theorem locality-of-integrals-lemma
  "forall(phi:[ii,uu],a,b:ii,
     a<b 
      and 
     integrable(phi) 
      and
     forall(x:ii, a<=x and x<b implies phi(x)=v0) 
      implies 
     forall(x:ii, a<=x and x<b implies integral(a,x,phi)=v0))"
  
  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof

   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) integral)
    (cut-with-single-formula "forsome(g:[ii,uu],primitive(phi,v0,a)=g)")
    (antecedent-inference "with(a:ii,phi:[ii,uu],
  forsome(g:[ii,uu],primitive(phi,v0,a)=g));")
    (backchain "with(g:[ii,uu],a:ii,phi:[ii,uu],primitive(phi,v0,a)=g);")
    (incorporate-antecedent "with(g:[ii,uu],a:ii,phi:[ii,uu],primitive(phi,v0,a)=g);")
    (apply-macete-with-minor-premises characterization-of-primitive)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forall(x,y:ii, (a<=x and x<b) and (a<=y and y<b) implies g(x)=g(y))")
    (backchain-backwards "with(a:ii,g:[ii,uu],g(a)=v0);")
    (backchain "with(g:[ii,uu],b,a:ii,
  forall(x,y:ii,
    (a<=x and x<b) and (a<=y and y<b) implies g(x)=g(y)));")
    simplify
    (apply-macete-with-minor-premises constant-on-subintervals-corollary)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("b" "a"))
    (incorporate-antecedent "with(g:[ii,uu],continuous(g));")
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    direct-and-antecedent-inference-strategy
    (backchain "with(g:[ii,uu],forall(x:ii,continuous%at%point(g,x)));")
    (backchain "with(phi,g:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(g,y)=phi(y)));")
    direct-inference
    (instantiate-existential ("b"))
    simplify
    (instantiate-existential ("b"))
    (instantiate-existential ("primitive(phi,v0,a)"))
    simplify
    (apply-macete-with-minor-premises integrability-condition)
    (instantiate-existential ("b"))

    )))

(def-theorem locality-of-integrals
  "forall(phi,psi:[ii,uu],a,b:ii,
     a<b 
      and 
     integrable(phi)
      and
     integrable(psi)
      and
     forall(x:ii, a<=x and x<b implies phi(x)=psi(x)) 
      implies 
     forall(x:ii, a<=x and x<b implies integral(a,x,phi)=integral(a,x,psi)))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof

   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "integral(a,x,lambda(x:ii,phi(x)-psi(x)))=v0")
    (incorporate-antecedent "with(psi,phi:[ii,uu],x,a:ii,
  integral(a,x,lambda(x:ii,phi(x)-psi(x)))=v0);")
    simplify
    (force-substitution "[-1]*psi(x)" "lambda(x:ii,[-1]*psi(x))(x)" (0))
    (apply-macete-with-minor-premises additivity-of-integral)
    (apply-macete-with-minor-premises homogeneity-of-integral)
    simplify
    (instantiate-existential ("b"))
    (apply-macete-with-minor-premises integrable-implies-integral-exists)
    (instantiate-existential ("b"))
    (apply-macete-with-minor-premises homogeneity-of-integral)
    simplify
    (apply-macete-with-minor-premises integrable-implies-integral-exists)
    (instantiate-existential ("b"))
    simplify
    (apply-macete-with-minor-premises locality-of-integrals-lemma)
    (unfold-single-defined-constant (0) integrable)
    (cut-with-single-formula "#(integral(a,b,lambda(x:ii,phi(x)+[-1]*psi(x))))")
    (incorporate-antecedent "with(psi,phi:[ii,uu],b,a:ii,
  #(integral(a,b,lambda(x:ii,phi(x)+[-1]*psi(x)))));")
    (unfold-single-defined-constant (0) integral)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("v0" "a" "b"))
    (force-substitution "[-1]*psi(x)" "lambda(x:ii,[-1]*psi(x))(x)" (0))
    (apply-macete-with-minor-premises additivity-of-integral)
    (apply-macete-with-minor-premises homogeneity-of-integral)
    simplify
    (apply-macete-with-minor-premises integrable-implies-integral-exists)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises integrable-implies-integral-exists)
    (apply-macete-with-minor-premises homogeneity-of-integral)
    simplify
    (apply-macete-with-minor-premises integrable-implies-integral-exists)

    )))
