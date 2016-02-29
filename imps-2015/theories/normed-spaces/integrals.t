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


(herald integrals)

(include-files 
 (files (imps theories/normed-spaces/derivatives)))


(def-constant primitive
  "lambda(phi:[ii,uu],c:uu,x:ii,
      iota(f:[ii,uu],
        total_q{f,[ii,uu]}
         and
        continuous(f)
         and 
        f(x)=c
         and 
        forall(y:ii,
          forsome(z:ii,y<z) implies deriv(f,y)=phi(y))))"
  (theory mappings-from-an-interval-to-a-normed-space))
  
(def-theorem characterization-of-primitive
  "forall(phi:[ii,uu],c:uu,x:ii,v:[ii,uu],
     forsome(y:ii,x<y)
      implies 
     primitive(phi,c,x)=v
      iff 
     (total_q{v,[ii,uu]}
      and
     continuous(v)
      and 
     v(x)=c
      and 
     forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=phi(y))))"
  
  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant (0) primitive)
    direct-inference
    direct-inference
    direct-inference
    (contrapose "with(a:[ii,uu],p:prop, iota(f:[ii,uu], p)=a)")
    (eliminate-defined-iota-expression 0 w)
    (contrapose "with(phi:[ii,uu],c:uu,x:ii,v:[ii,uu],
  forsome(x_0:ii,not(#(v(x_0))))
   or 
  not(continuous(v))
   or 
  not(v(x)=c)
   or 
  forsome(y:ii,
    forsome(z:ii,y<z) and not(deriv(v,y)=phi(y))));")
    (backchain-backwards "with(v,w:[ii,uu],w=v);")
    (backchain-backwards "with(v,w:[ii,uu],w=v);")
    (backchain-backwards "with(v,w:[ii,uu],w=v);")
    (backchain-backwards "with(v,w:[ii,uu],w=v);")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    extensionality
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises mean-value-theorem-corollary-1)
    direct-and-antecedent-inference-strategy
    (backchain "with(phi:[ii,uu],c:uu,x:ii,v:[ii,uu],
  total_q{v,[ii,uu]}
   and 
  continuous(v)
   and 
  v(x)=c
   and 
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=phi(y)));")
    direct-inference
    auto-instantiate-existential
    (backchain "with(phi,b:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(b,y)=phi(y)));")
    (instantiate-existential ("x" "y"))

    )))

(def-constant integral
  "lambda(a,b:ii,phi:[ii,uu], primitive(phi,v0,a)(b))"
  (theory mappings-from-an-interval-to-a-normed-space))


(def-theorem primitive-existence
  "forall(phi:[ii,uu],c:uu,x:ii,
     forsome(y:ii,x<y)
      implies 
     #(primitive(phi,c,x))
     iff
    forsome(v:[ii,uu], 
      total_q{v,[ii,uu]}
        and
      continuous(v)
        and 
      forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=phi(y))))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
      (cut-with-single-formula "forsome(v:[ii,uu],primitive(phi,c,x)=v)")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(v:[ii,uu],p));")
	(incorporate-antecedent "with(v,f:[ii,uu],f=v);")
	(apply-macete-with-minor-premises characterization-of-primitive)
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (0)")
	  direct-and-antecedent-inference-strategy (instantiate-existential ("v"))
	  )
	auto-instantiate-existential
	)
      (instantiate-existential ("primitive(phi,c,x)"))
      )
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0 0)")
      (cut-with-single-formula "primitive(phi,c,x)=lambda(z:ii,c+v(z)-v(x))")
      (apply-macete-with-minor-premises characterization-of-primitive)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)") beta-reduce-repeatedly
	insistent-direct-inference-strategy
	(block 
	  (script-comment "`insistent-direct-inference-strategy' at (0 0)")
	  beta-reduce-repeatedly simplify
	  )
	(block 
	  (script-comment "`insistent-direct-inference-strategy' at (1)")
	  (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
	  (force-substitution "c+v(z)-v(x)" "lambda(z:ii,c-v(x))(z)+v(z)" (0))
	  (block 
	    (script-comment "`force-substitution' at (0)")
	    (apply-macete-with-minor-premises ns-sum-of-continuous-is-continuous)
	    (apply-macete-with-minor-premises tr%ms-constant-continuous)
	    direct-and-antecedent-inference-strategy
	    (incorporate-antecedent "with(v:[ii,uu],continuous(v));")
	    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
	    direct-and-antecedent-inference-strategy
	    )
	  simplify
	  )
	simplify
	(block 
	  (script-comment "`insistent-direct-inference-strategy' at (3 0 0)")
	  (force-substitution "c+v(z)-v(x)" "lambda(z:ii,c-v(x))(z)+v(z)" (0))
	  (block 
	    (script-comment "`force-substitution' at (0)")
	    (apply-macete-with-minor-premises additivity-of-deriv)
	    (block 
	      (script-comment "`apply-macete-with-minor-premises' at (0)")
	      (apply-macete-with-minor-premises deriv-of-constant) simplify
	      )
	    simplify simplify
	    )
	  simplify
	  ) )
      auto-instantiate-existential
      )
    )))


(def-theorem endpoint-additivity-of-integral
  "forall(a,b,c:ii,f:[ii,uu],
    #(integral(a,b,f))
      and 
     #(integral(b,c,f))
      and 
     forsome(y:ii,a<y and b<y)
      implies 
     integral(a,c,f)=integral(a,b,f)+integral(b,c,f))"
  
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(v,w:[ii,uu],primitive(f,v0,a)=v and primitive(f,v0,b)=w)")
    (antecedent-inference "with(b,a:ii,f:[ii,uu],
  forsome(v,w:[ii,uu],
    primitive(f,v0,a)=v and primitive(f,v0,b)=w));")
    (backchain "with(p,q:prop, p and q)")
    (backchain "with(p,q:prop, p and q)")
    (backchain "with(p,q:prop, p and q)")
    (incorporate-antecedent "with(p,q:prop, p and q)")
    (apply-macete-with-minor-premises characterization-of-primitive)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "v=lambda(c:ii,lambda(c:ii,v(b))(c)+w(c))")
    simplify
    (backchain "with(w:[ii,uu],b:ii,v:[ii,uu],
  v=lambda(c:ii,lambda(c:ii,v(b))(c)+w(c)));")
    beta-reduce-repeatedly
    simplify
    extensionality
    insistent-direct-inference
    insistent-direct-inference
    (apply-macete-with-minor-premises mean-value-theorem-corollary-1)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    beta-reduce-repeatedly
    simplify
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    (apply-macete-with-minor-premises ns-sum-of-continuous-is-continuous)
    (apply-macete-with-minor-premises tr%ms-constant-continuous)
    (incorporate-antecedent "with(w:[ii,uu],continuous(w));")
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    (apply-macete-with-minor-premises additivity-of-deriv)
    (apply-macete-with-minor-premises deriv-of-constant)
    (backchain "with(f,w:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(w,y)=f(y)));")
    (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
    direct-and-antecedent-inference-strategy
    direct-inference
    auto-instantiate-existential
    (instantiate-existential ("y_$0"))
    simplify
    (cut-with-single-formula "deriv(w,x)=f(x)")
    (backchain "with(f,w:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(w,y)=f(y)));")
    (instantiate-existential ("z"))
    (cut-with-single-formula "deriv(w,x)=f(x)")
    (backchain "with(f,w:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(w,y)=f(y)));")
    (apply-macete-with-minor-premises deriv-of-constant)
    beta-reduce-repeatedly
    (instantiate-existential ("b" "y"))
    (backchain "with(b:ii,w:[ii,uu],w(b)=v0);")
    simplify
    (instantiate-existential ("y"))
    (instantiate-existential ("y"))
    (instantiate-existential ("primitive(f,v0,a)" "primitive(f,v0,b)"))

)))


(def-theorem integral-on-null-interval-is-zero
  "forall(a:ii,f:[ii,uu],
    #(integral(a,a,f))
      and 
     forsome(y:ii,a<y)
      implies 
     integral(a,a,f)=v0)"
  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof

   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "integral(a,a,f)=integral(a,a,f)+integral(a,a,f)")
    (incorporate-antecedent "with(f:[ii,uu],a:ii,
  integral(a,a,f)=integral(a,a,f)+integral(a,a,f));")
    simplify
    (apply-macete-with-minor-premises endpoint-additivity-of-integral)
    auto-instantiate-existential


    )))

;;Make integrals more readable:

(def-print-syntax integral
  tex
  (token " \\int ")
  (method present-tex-interval-iteration-operator)
  (binding 50))

(make-tex-correspondence "ii" "{ \\bf I}")

(def-theorem mean-value-theorem-for-integrals-preliminary-form
  "forall(a,b:ii,f:[ii,uu],m:rr,
     0<m
      and 
     forsome(y:ii,a<y)
      and 
     #(integral(a,b,f))
      and 
     forall(x:ii,norm(f(x))<=m)
      implies 
     norm(integral(a,b,f))<=m*abs(b-a))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (

    (unfold-single-defined-constant (0 1) integral)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(v:[ii,uu], primitive(f,v0,a)=v)")
    (antecedent-inference "with(p:prop,forsome(v:[ii,uu],p))")
    (backchain "with(v:[ii,uu],a:ii,f:[ii,uu],primitive(f,v0,a)=v);")
    (incorporate-antecedent "with(v:[ii,uu],a:ii,f:[ii,uu],primitive(f,v0,a)=v);")
    (apply-macete-with-minor-premises characterization-of-primitive)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "lipschitz%bound(v,m)")
    (incorporate-antecedent "with(m:rr,v:[ii,uu],lipschitz%bound(v,m));")
    (incorporate-antecedent "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
    (unfold-single-defined-constant (0) uu%lipschitz%bound)
    (unfold-single-defined-constant (0) uu%%lipschitz%bound%on)
    direct-and-antecedent-inference-strategy
    (force-substitution "v(b)" "v(b)-v(a)" (0))
    (backchain "with(m:rr,v:[ii,uu],
  forall(x_$0,y_$0:ii,
    x_$0 in sort_to_indic{ii} and y_$0 in sort_to_indic{ii}
     implies 
    norm(v(x_$0)-v(y_$0))<=m*abs(x_$0-y_$0)));")
    simplify
    simplify
    (apply-macete-with-minor-premises mean-value-theorem)
    direct-and-antecedent-inference-strategy
    (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
    direct-inference
    (instantiate-existential ("y_$0"))
    (backchain "with(m:rr,f:[ii,uu],forall(x:ii,norm(f(x))<=m));")
    auto-instantiate-existential
    (instantiate-existential ("primitive(f,v0,a)"))

    )))




(def-theorem additivity-of-integral
  "forall(a,b:ii,f,g:[ii,uu],
    #(integral(a,b,f))
     and 
    #(integral(a,b,g))
     and 
    forsome(y:ii,a<y)
     implies 
    integral(a,b,lambda(x:ii,f(x)+g(x)))
    =integral(a,b,f)+integral(a,b,g))"
  
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(v,w:[ii,uu],primitive(f,v0,a)=v and primitive(g,v0,a)=w)")
    (antecedent-inference "with(p,q:prop, forsome(v,w:[ii,uu], p and q))")
    (backchain "with(p,q:prop, p and q)")
    (backchain "with(p,q:prop, p and q)")
    (cut-with-single-formula "primitive(lambda(x:ii,f(x)+g(x)),v0,a)=lambda(b:ii,v(b)+w(b))")
    simplify
    (incorporate-antecedent "with(p,q:prop, p and q)")
    (apply-macete-with-minor-premises characterization-of-primitive)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    simplify
    (incorporate-antecedent "with(v:[ii,uu],continuous(v));")
    (incorporate-antecedent "with(w:[ii,uu],continuous(w));")
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    (apply-macete-with-minor-premises ns-sum-of-continuous-is-continuous)
    direct-and-antecedent-inference-strategy
    (backchain "with(v:[ii,uu],forall(x:ii,continuous%at%point(v,x)));")
    (backchain "with(w:[ii,uu],forall(x:ii,continuous%at%point(w,x)));")
    simplify
    (apply-macete-with-minor-premises additivity-of-deriv)
    simplify
    (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
    (backchain "with(g,w:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(w,y)=g(y)));")
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (weaken (14 15 13 11 10 9 7 6 3 2))
    (cut-with-single-formula "deriv(v,y_$0)=f(y_$0) and deriv(w,y_$0)=g(y_$0)")
    simplify
    direct-inference
    (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
    auto-instantiate-existential
    (backchain "with(g,w:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(w,y)=g(y)));")
    (weaken (1 2 5 6 8 9 10 12 13 14))
    (cut-with-single-formula "deriv(w,y_$0)=g(y_$0)")
    (backchain "with(g,w:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(w,y)=g(y)));")
    auto-instantiate-existential
    (weaken (8 9 10 13 14 5 1 2 2 5))
    (cut-with-single-formula "deriv(v,y_$0)=f(y_$0)")
    (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
    auto-instantiate-existential
    auto-instantiate-existential
    auto-instantiate-existential
    auto-instantiate-existential
    (instantiate-existential ("primitive(f,v0,a)" "primitive(g,v0,a)"))

    )))

(comment;; new proof script


 unfold-defined-constants
 direct-and-antecedent-inference-strategy
 (cut-with-single-formula "forsome(v,w:[ii,uu],primitive(f,v0,a)=v and primitive(g,v0,a)=w)")
 (antecedent-inference "with(p:prop,forsome(v,w:[ii,uu],p));")
 (backchain "with(p:prop,p and p);")
 (backchain "with(p:prop,p and p);")
 (cut-with-single-formula "primitive(lambda(x:ii,f(x)+g(x)),v0,a)=lambda(b:ii,v(b)+w(b))")
 simplify
 (incorporate-antecedent "with(p:prop,p and p);")
 (apply-macete-with-minor-premises characterization-of-primitive)
 direct-and-antecedent-inference-strategy
 insistent-direct-inference
 simplify
 (incorporate-antecedent "with(v:[ii,uu],continuous(v));")
 (incorporate-antecedent "with(w:[ii,uu],continuous(w));")
 (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
 (apply-macete-with-minor-premises ns-sum-of-continuous-is-continuous)
 direct-and-antecedent-inference-strategy
 simplify
 (apply-macete-with-minor-premises additivity-of-deriv)
 simplify
 (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
 (backchain "with(g,w:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(w,y)=g(y)));")
 direct-and-antecedent-inference-strategy
 auto-instantiate-existential
 (weaken (14 15 13 11 10 9 7 6 3 2))
 (cut-with-single-formula "deriv(v,y_$0)=f(y_$0) and deriv(w,y_$0)=g(y_$0)")
 simplify
 direct-inference
 (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
 auto-instantiate-existential
 (backchain "with(g,w:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(w,y)=g(y)));")
 (weaken (1 2 5 6 8 9 10 12 13 14))
 (cut-with-single-formula "deriv(w,y_$0)=g(y_$0)")
 (backchain "with(g,w:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(w,y)=g(y)));")
 auto-instantiate-existential
 (weaken (8 9 10 13 14 5 1 2 2 5))
 (cut-with-single-formula "deriv(v,y_$0)=f(y_$0)")
 (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
 auto-instantiate-existential
 auto-instantiate-existential
 auto-instantiate-existential
 auto-instantiate-existential
 (instantiate-existential ("primitive(f,v0,a)" "primitive(g,v0,a)"))


 )
(def-theorem homogeneity-of-integral
  "forall(a,b:ii,c:rr,f:[ii,uu],
    #(integral(a,b,f))
     and 
    forsome(y:ii,a<y)
     implies 
    integral(a,b,lambda(x:ii,c*f(x)))=c*integral(a,b,f))"
  
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(v:[ii,uu],primitive(f,v0,a)=v)")
    (antecedent-inference "with(p:prop, forsome(v:[ii,uu], p))")
    (backchain "with(a,b:[ii,uu],a=b)")
    (cut-with-single-formula "primitive(lambda(x:ii,c*f(x)),v0,a)=lambda(b:ii, c*v(b))")
    simplify
    (incorporate-antecedent "with(a,b:[ii,uu],a=b)")
    (apply-macete-with-minor-premises characterization-of-primitive)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    simplify
    (incorporate-antecedent "with(v:[ii,uu],continuous(v));")
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    (apply-macete-with-minor-premises ns-multiple-of-continuous-is-continuous)
    simplify
    (apply-macete-with-minor-premises homogeneity-of-deriv)
    (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
    direct-inference
    auto-instantiate-existential
    simplify
    (cut-with-single-formula "deriv(v,y_$0)=f(y_$0)")
    (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
    (cut-with-single-formula "deriv(v,y_$0)=f(y_$0)")
    (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
    auto-instantiate-existential
    auto-instantiate-existential
    (instantiate-existential ("primitive(f,v0,a)"))

    )))


(def-theorem ns-vector-multiple-of-continuous-is-continuous
  "forall(f:[ii,rr], x:ii, a:uu,
     continuous%at%point(f,x)
      implies 
     continuous%at%point(lambda(x:ii,f(x)*a),x))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (


    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (case-split ("a=v0"))
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" ("1"))
    (simplify-antecedent "not(0<1);")
    (instantiate-existential ("delta"))
    simplify
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" ("eps_$0/norm(a)"))
    (contrapose "not(0<eps_$0/norm(a))")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (weaken (0 2))
    (cut-with-single-formula "not(norm(a)=0)")
    simplify
    (apply-macete-with-minor-premises norm-zero)
    (instantiate-existential ("delta"))
    (force-substitution "f(x)*a-f(y_$0)*a" "(f(x)-f(y_$0))*a" (0))
    (apply-macete-with-minor-premises norm-scalar-multiplication)
    (instantiate-universal-antecedent "with(p:prop, forall(y:ii, p))" ("y_$0"))
    (incorporate-antecedent "abs(f(x)-f(y_$0))<=eps_$0/norm(a)")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    (weaken (0 1 3))
    simplify
    (cut-with-single-formula "0<norm(a)")
    simplify
    (weaken (1 2))


    )))



(def-theorem integral-of-a-constant
  "forall(a,b:ii,c:uu, forsome(y:ii,a<y) implies integral(a,b,lambda(t:ii,c))=(b-a)*c)"
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "primitive(lambda(t:ii,c),v0,a)=lambda(b:ii,(b-a)*c)")
    simplify
    (apply-macete-with-minor-premises characterization-of-primitive)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    direct-and-antecedent-inference-strategy
    (force-substitution "(b-a)*c" "lambda(b:ii,b*c)(b)+lambda(b:ii,a*([-1]*c))(b)" (0))
    (apply-macete-with-minor-premises ns-sum-of-continuous-is-continuous)
    (apply-macete-with-minor-premises tr%ms-constant-continuous)
    (force-substitution "b" "lambda(b:ii,b)(b)" (0))
    (apply-macete-with-minor-premises ns-vector-multiple-of-continuous-is-continuous)
    (apply-macete-with-minor-premises tr%lipschitz-bound-is-continuous)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("1"))
    (unfold-single-defined-constant (0) lipschitz%bound_2)
    (unfold-single-defined-constant (0) lipschitz%bound%on_2)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    beta-reduce-repeatedly
    simplify
    simplify
    (force-substitution "(b-a)*c" "b*c+[-1]*a*c" (0))
    (apply-macete-with-minor-premises derivative-of-a-linear-map)
    beta-reduce-repeatedly
    (instantiate-existential ("z"))
    simplify
    auto-instantiate-existential


    )))


(def-theorem mean-value-theorem-for-integrals
  "forall(a,b:ii,f:[ii,uu],m:rr,
     forsome(y:ii,a<y)
      and 
     #(integral(a,b,f))
      and 
     forall(x:ii,norm(f(x))<=m)
      implies 
     norm(integral(a,b,f))<=m*abs(b-a))"

  (theory mappings-from-an-interval-to-a-normed-space)
  (proof

   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "m<0 or m=0 or 0<m")
    (antecedent-inference "with(m:rr,m<0 or m=0 or 0<m);")
    (cut-with-single-formula "norm(f(x))<=m")
    (cut-with-single-formula "0<=norm(f(x))")
    simplify
    (apply-macete-with-minor-premises positivity-of-norm)
    (backchain "with(m:rr,f:[ii,uu],forall(x:ii,norm(f(x))<=m));")
    simplify
    (cut-with-single-formula "f=lambda(x:ii,v0)")
    (backchain "with(f:[ii,uu],f=lambda(x:ii,v0));")
    (apply-macete-with-minor-premises integral-of-a-constant)
    simplify
    auto-instantiate-existential
    extensionality
    direct-and-antecedent-inference-strategy
    beta-reduce-repeatedly
    (cut-with-single-formula "norm(f(x_0))=0")
    (incorporate-antecedent "with(x:ii,f:[ii,uu],norm(f(x_0))=0);")
    (apply-macete-with-minor-premises norm-zero)
    (cut-with-single-formula "0<=norm(f(x_0))")
    simplify
    (apply-macete-with-minor-premises positivity-of-norm)
    (apply-macete-with-minor-premises mean-value-theorem-for-integrals-preliminary-form)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    simplify


    )))

;; The following two scripts are defunct.

(comment
 (def-script epsilon/n-argument 1	;eps is a string.
   (
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" ($1))

    ))


 (def-script instantiate-with-smaller-value 2
   (
    (cut-with-single-formula (% "min(~A,~A)<=~A and min(~A,~A)<=~A" $1 $2 $1 $1 $2 $2))
    (instantiate-existential ((% "min(~A,~A)" $1 $2)))
    ))
 )


(def-theorem splicing-pointwise-continuous-functions
  "forall(f,g:[ii,pp],x:ii,
     continuous%at%point(f,x)
      and 
     continuous%at%point(g,x)
      and 
     f(x)=g(x)
      implies 
     continuous%at%point(lambda(t:ii,if(t<=x, f(t), g(t))),x))"
  (theory mappings-from-an-interval)
  (proof
   (


    (force-substitution "t<=x" "t in indic{t:ii, t<=x}" (0))
    (move-to-sibling 1)
    simplify-insistently
    (apply-macete-with-minor-premises tr%splicing-continuous-functions-lemma-1)
    ))
  (usages transportable-macete))


(def-theorem splicing-continuous-functions
  "forall(f,g:[ii,pp],x:ii,
     total_q{f,[ii,pp]}
      and
     total_q{g,[ii,pp]}
      and
     continuous(f)
      and 
     continuous(g)
      and 
     f(x)=g(x)
      implies 
     continuous(lambda(t:ii,if(t<=x, f(t), g(t)))))"
  (theory mappings-from-an-interval)
  (proof
   (


    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    direct-and-antecedent-inference-strategy
    (case-split ("x_$0=x"))

    (block (force-substitution "t<=x" "t in indic{t:ii, t<=x}" (0))
	   (move-to-sibling 1)
	   simplify-insistently
	   (apply-macete-with-minor-premises tr%splicing-continuous-functions-lemma-1)
	   simplify)
    (apply-macete-with-minor-premises tr%splicing-continuous-functions-lemma-2)
    (apply-macete-with-minor-premises tr%open-ball-membership-condition)
    beta-reduce-repeatedly
    (case-split ("x_$0<x"))

    (block (instantiate-existential ("f"))
	   (instantiate-existential ("x-x_$0"))
	   simplify
	   (cut-with-single-formula "z_$0<=x")
	   simplify
	   (contrapose "with(x_$0,x:ii,r:rr,abs(r)<x-x_$0);")
	   (unfold-single-defined-constant (0) abs)
	   simplify)
    (block (instantiate-existential ("g"))
	   (instantiate-existential ("x_$0-x"))
	   simplify
	   (cut-with-single-formula "x<z_$0")
	   simplify
	   (contrapose "with(x,x_$0:ii,r:rr,abs(r)<x_$0-x);")
	   (unfold-single-defined-constant (0) abs)
	   simplify)
    (block (script-comment "totality")
	   simplify-insistently
	   direct-and-antecedent-inference-strategy
	   (case-split ("x_0<=x"))
	   simplify
	   simplify))
   )
  (usages transportable-macete))

(def-constant integrable
  "lambda(f:[ii,uu], forsome(c:uu, x,y:ii, x<y and #(primitive(f,c,x))))"
  (theory mappings-from-an-interval-to-a-normed-space))


(def-theorem integrability-condition
  "forall(f:[ii,uu], integrable(f) implies
    forall(c:uu, x,y:ii, x<y implies #(primitive(f,c,x))))"

  (usages transportable-macete)
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (

    (unfold-single-defined-constant (0) integrable)
    (apply-macete-with-minor-premises primitive-existence)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    auto-instantiate-existential

    )))


(def-theorem integrable-implies-integral-exists
  "forall(f:[ii,uu], integrable(f) implies 
     forall(x,y,z:ii, x<z implies #(integral(x,y,f))))"
  (usages transportable-macete)
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) integral)
    (cut-with-single-formula "forsome(v:[ii,uu],primitive(f,v0,x)=v)")
    (antecedent-inference "with(x:ii,f:[ii,uu],forsome(v:[ii,uu],primitive(f,v0,x)=v));")
    (backchain "with(v:[ii,uu],x:ii,f:[ii,uu],primitive(f,v0,x)=v);")
    (incorporate-antecedent "with(v:[ii,uu],x:ii,f:[ii,uu],primitive(f,v0,x)=v);")
    (apply-macete-with-minor-premises characterization-of-primitive)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (cut-with-single-formula "#(primitive(f,v0,x))")
    (instantiate-existential ("primitive(f,v0,x)"))
    (apply-macete-with-minor-premises integrability-condition)
    (instantiate-existential ("z"))

    )))

(def-theorem integrable-implies-integral-is-continuous
  "forall(f:[ii,uu],x,y:ii, integrable(f) and x<y implies
       continuous(lambda(y:ii, integral(x,y,f))))"
  (usages transportable-macete)
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) integral)
    (cut-with-single-formula "forsome(v:[ii,uu], primitive(f,v0,x)=v)")
    (antecedent-inference "with(x:ii,f:[ii,uu],forsome(v:[ii,uu],primitive(f,v0,x)=v));")
    (backchain "with(v:[ii,uu],x:ii,f:[ii,uu],primitive(f,v0,x)=v);")
    (apply-macete-with-minor-premises tr%unary-eta-reduction)
    (incorporate-antecedent "with(v:[ii,uu],x:ii,f:[ii,uu],primitive(f,v0,x)=v);")
    (apply-macete-with-minor-premises characterization-of-primitive)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (cut-with-single-formula "#(primitive(f,v0,x))")
    (instantiate-existential ("primitive(f,v0,x)"))
    (apply-macete-with-minor-premises integrability-condition)
    (instantiate-existential ("y"))

    
    )))

(def-theorem fundamental-theorem-of-calculus
  "forall(f:[ii,uu],a,b:ii, forsome(y,z:ii, a<y and b<z) and integrable(f) 
             implies deriv(lambda(y:ii,integral(a,y,f)),b)=f(b))"
  (usages transportable-macete)
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof

   (
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) integral)
    (cut-with-single-formula "forsome(v:[ii,uu], primitive(f,v0,a)=v)")
    (antecedent-inference "with(a:ii,f:[ii,uu],forsome(v:[ii,uu],primitive(f,v0,a)=v));")
    (backchain "with(v:[ii,uu],a:ii,f:[ii,uu],primitive(f,v0,a)=v);")
    (apply-macete-with-minor-premises tr%unary-eta-reduction)
    (incorporate-antecedent "with(v:[ii,uu],a:ii,f:[ii,uu],primitive(f,v0,a)=v);")
    (apply-macete-with-minor-premises characterization-of-primitive)
    direct-and-antecedent-inference-strategy
    (backchain "with(f,v:[ii,uu],
  forall(y:ii,forsome(z:ii,y<z) implies deriv(v,y)=f(y)));")
    auto-instantiate-existential
    auto-instantiate-existential
    (cut-with-single-formula "#(primitive(f,v0,a))")
    (instantiate-existential ("primitive(f,v0,a)"))
    (apply-macete-with-minor-premises integrability-condition)
    (instantiate-existential ("y"))

    )))

(def-theorem piecewise-integrable-is-integrable
  "forall(f,g:[ii,uu], x:ii, integrable(f) and integrable(g) and forsome(z:ii, x<z) implies 
            integrable(lambda(y:ii,if(y<x,f(y),g(y)))))"
  (usages transportable-macete)
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (

    direct-inference
    (case-split ("forsome(y:ii,x<y)"))
    (antecedent-inference "with(x:ii,forsome(y:ii,x<y));")
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) integrable)
    (apply-macete-with-minor-premises primitive-existence)
    (instantiate-existential ("c_$0" "x" "y"))
    (instantiate-existential ("lambda(y:ii, if(y<=x,integral(x,y,f),integral(x,y,g)))"))
    insistent-direct-inference
    beta-reduce-repeatedly
    (cut-with-single-formula "#(integral(x,x_$0,f)) and #(integral(x,x_$0,g))")
    simplify
    (apply-macete-with-minor-premises integrable-implies-integral-exists)
    direct-inference
    (instantiate-existential ("y"))
    (instantiate-existential ("y"))
    (force-substitution "if(y<=x, integral(x,y,f), integral(x,y,g))" "if(y<=x, lambda(y:ii,integral(x,y,f))(y), 
                       lambda(y:ii,integral(x,y,g))(y))" (0))
    (apply-macete-with-minor-premises tr%splicing-continuous-functions)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    beta-reduce-repeatedly
    insistent-direct-inference
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises integrable-implies-integral-is-continuous)
    (apply-macete-with-minor-premises integrable-implies-integral-is-continuous)
    (instantiate-existential ("y"))
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises integral-on-null-interval-is-zero)
    (apply-macete-with-minor-premises integrable-implies-integral-exists)
    auto-instantiate-existential
    (apply-macete-with-minor-premises integrable-implies-integral-exists)
    beta-reduce-repeatedly
    (case-split ("y_$0<x"))
    simplify
    (force-substitution "deriv(lambda(y:ii,
          if(y<=x, integral(x,y,f), integral(x,y,g))),
        y_$0)" "deriv(lambda(y:ii, integral(x,y,f)),y_$0)" (0))
    (assume-theorem fundamental-theorem-of-calculus)
    (backchain "forall(f:[ii,uu],a,b:ii,
  forsome(y,z:ii,a<y and b<z) and integrable(f)
   implies 
  deriv(lambda(y:ii,integral(a,y,f)),b)=f(b));")
    direct-inference
    (instantiate-existential ("y" "z_$1"))
    (apply-macete-with-minor-premises locality-of-derivative)
    (instantiate-existential ("x"))
    simplify
    (apply-macete-with-minor-premises integrable-implies-integral-exists)
    simplify
    (force-substitution "deriv(lambda(y:ii,
          if(y<=x, integral(x,y,f), integral(x,y,g))),
        y_$0)" "deriv(lambda(y:ii,integral(x,y,g)),y_$0)" (0))
    (assume-theorem fundamental-theorem-of-calculus)
    (backchain "forall(f:[ii,uu],a,b:ii,
  forsome(y,z:ii,a<y and b<z) and integrable(f)
   implies 
  deriv(lambda(y:ii,integral(a,y,f)),b)=f(b));")
    direct-inference
    (instantiate-existential ("y" "z_$1"))
    (apply-macete-with-minor-premises locality-of-derivative)
    beta-reduce-repeatedly
    (instantiate-existential ("z_$1"))
    (case-split ("x=t"))
    simplify
    (apply-macete-with-minor-premises integral-on-null-interval-is-zero)
    (apply-macete-with-minor-premises integrable-implies-integral-exists)
    (instantiate-existential ("y"))
    (instantiate-existential ("z_$1"))
    (apply-macete-with-minor-premises integrable-implies-integral-exists)
    (instantiate-existential ("z_$1"))
    simplify
    (apply-macete-with-minor-premises integrable-implies-integral-exists)
    (instantiate-existential ("y_$0"))
    direct-inference

    )))



