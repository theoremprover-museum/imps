(include-files
 (files (imps theories/reals/exponentiation)))

(def-theorem second-root-of-zero
  "nth%root(2,0)=0"
  (theory h-o-real-arithmetic)
  (usages rewrite)
  (proof
   (

    (apply-macete-with-minor-premises nth%root-of-zero)

    )))

(def-theorem sqrt-is-an-nth%root-special-case
  "forall(x:rr,sqrt(x)==nth%root(2,x))"
  reverse
  (usages rewrite)
  (theory h-o-real-arithmetic)
  (proof
   (

    unfold-defined-constants
    simplify

    )))

(def-theorem defined-nth%root-is-nonnegative
  "forall(n:zz,x:rr, 1<=n implies #(nth%root(n,x)) iff 0<=x)"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (block 
      (script-comment 
       "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      (cut-with-single-formula "forsome(y:rr, nth%root(n,x)=y)")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(y:rr,p));")
	(incorporate-antecedent "with(y,r:rr,r=y);")
	(apply-macete-with-minor-premises 
	 iota-free-characterization-of-nth%root)
	direct-and-antecedent-inference-strategy
	(backchain-backwards "with(x,r:rr,r=x);")
	(apply-macete-with-minor-premises weak-positivity-for-r^n)
	simplify)
      (instantiate-existential ("nth%root(n,x)")))
    (block 
      (script-comment 
       "`direct-and-antecedent-inference-strategy' at (0 0 1)")
      (apply-macete-with-minor-premises nth%root%existence)
      simplify)

    )))

(def-theorem positivity-for-products-of-negatives
  "forall(x,y:rr, x <= 0 and y <= 0 implies 0 <= x*y)"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (force-substitution "x*y" "(-x)*(-y)" (0))
    (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises positivity-for-products)
      simplify)
    simplify

    )))

(def-theorem strict-positivity-for-products-of-negatives
  "forall(x,y:rr, x < 0 and y < 0 implies 0 < x*y)"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (force-substitution "x*y" "(-x)*(-y)" (0))
    (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises strict-positivity-for-products)
      simplify)
    simplify

    )))

(def-theorem negativity-for-products
  "forall(x,y:rr, 0 <= x and y <= 0 implies x*y <= 0)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (instantiate-theorem positivity-for-products ("x" "-y"))
    (simplify-antecedent "with(p:prop,p);")
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`instantiate-theorem' at (0 0 1)")
      direct-and-antecedent-inference-strategy
      simplify)

    )))

(def-theorem strict-negativity-for-products
  "forall(x,y:rr, 0 < x and y < 0 implies x*y < 0)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (instantiate-theorem strict-positivity-for-products ("x" "-y"))
    (simplify-antecedent "with(p:prop,p);")
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`instantiate-theorem' at (0 0 1)")
      direct-and-antecedent-inference-strategy
      simplify)

    )))

(def-theorem bifurcate-<=-inequality
  "forall(x,y:rr, x <= y iff (x = y or x < y))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify

    )))

(def-theorem bifurcate->=-inequality
  "forall(x,y:rr, x >= y iff (x = y or x > y))"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    (unfold-single-defined-constant-globally >=)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    (block 
      (script-comment 
       "`direct-and-antecedent-inference-strategy' at (0 1 1)")
      (incorporate-antecedent "with(p:prop,p);")
      simplify)

    )))

(def-theorem reverse-zero-before-=
  "forall(x:rr, 0 = x iff x = 0)"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy

    )))

(def-theorem reverse-zero-before-<
  "forall(x:rr, 0 < x iff x > 0)"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    simplify
    (block 
      (script-comment 
       "`direct-and-antecedent-inference-strategy' at (0 1)")
      (incorporate-antecedent "with(p:prop,p);")
      simplify)direct-and-antecedent-inference-strategy
    simplify

    )))

(def-theorem reverse-zero-before-<=
  "forall(x:rr, 0 <= x iff x >= 0)"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    simplify
    (block 
      (script-comment 
       "`direct-and-antecedent-inference-strategy' at (0 1)")
      (incorporate-antecedent "with(p:prop,p);")
      simplify)

    )))

(def-theorem reverse-zero-before->
  "forall(x:rr, 0 > x iff x < 0)"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (block 
      (script-comment 
       "`direct-and-antecedent-inference-strategy' at (0 0)")
      (incorporate-antecedent "with(p:prop,p);")
      simplify)
    simplify

    )))

(def-theorem reverse-zero-before->=
  "forall(x:rr, 0 >= x iff x <= 0)"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (block 
      (script-comment 
       "`direct-and-antecedent-inference-strategy' at (0 0)")
      (incorporate-antecedent "with(p:prop,p);")
      simplify)
    simplify

    )))

(def-theorem bifurcate-product-equation
  "forall(x,y:rr, x*y = 0 iff (x = 0 or y = 0))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises cancel)

    )))

(def-theorem bifurcate-product-<-inequality
  "forall(x,y:rr, x*y < 0 
    iff 
   ((x < 0 and y > 0) or (x > 0 and y < 0)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-inference
    direct-inference
    (block 
      (script-comment "`direct-inference' at (0)")
      (cut-with-single-formula "0<x or x= 0 or x<0")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(cut-with-single-formula "0<y or y= 0 or y<0")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (antecedent-inference-strategy (0 1))
	  (simplify-antecedent "with(r:rr,r<0);")
	  (simplify-antecedent "with(r:rr,r<0);")
	  simplify
	  (simplify-antecedent "with(r:rr,r<0);")
	  (simplify-antecedent "with(r:rr,r<0);")
	  (simplify-antecedent "with(x:rr,x<0);")
	  simplify
	  (simplify-antecedent "with(y:rr,y<0);")
	  (block 
	    (script-comment "`antecedent-inference-strategy' at (2 2)")
	    (simplify-antecedent "with(x:rr,x<0);")
	    (simplify-antecedent "with(y,x:rr,x*y<0);")))
	simplify)
      simplify)
    (block 
      (script-comment "`direct-inference' at (1)")
      (antecedent-inference "with(p:prop,p);")
      (block 
	(script-comment "`antecedent-inference' at (0)")
	(instantiate-theorem strict-negativity-for-products ("y" "x"))
	(block 
	  (script-comment "`instantiate-theorem' at (0 0 0)")
	  (contrapose "with(p:prop,not(p));")
	  (antecedent-inference "with(p:prop,p and p);")
	  (incorporate-antecedent "with(y:rr,y>0);")
	  simplify)
	(apply-macete-with-minor-premises 
	 commutative-law-for-multiplication))
      (block 
	(script-comment "`antecedent-inference' at (1)")
	(apply-macete-with-minor-premises 
	 strict-negativity-for-products)
	direct-inference
	(antecedent-inference "with(p:prop,p);")
	(incorporate-antecedent "with(x:rr,x>0);")
	simplify))

    )))

(def-theorem bifurcate-product-<=-inequality
  "forall(x,y:rr, x*y <= 0 
    iff 
   ((x <= 0 and y >= 0) or (x >= 0 and y <= 0)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises bifurcate-<=-inequality)
    (apply-macete-with-minor-premises bifurcate->=-inequality)
    (apply-macete-with-minor-premises bifurcate-product-equation)
    (apply-macete-with-minor-premises bifurcate-product-<-inequality)
    direct-and-antecedent-inference-strategy
    simplify
    (simplify-antecedent "with(y:rr,not(y>0));")
    (simplify-antecedent "with(y:rr,not(y>0));")

    )))

(def-theorem bifurcate-product->-inequality
  "forall(x,y:rr, x*y > 0 
    iff 
   ((x < 0 and y < 0) or (x > 0 and y > 0)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-inference
    direct-inference
    (block 
      (script-comment "`direct-inference' at (0)")
      (cut-with-single-formula "0<x or x= 0 or x<0")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(cut-with-single-formula "0<y or y= 0 or y<0")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (antecedent-inference-strategy (0 1))
	  (block 
	    (script-comment "`antecedent-inference-strategy' at (0 0)")
	    (simplify-antecedent "with(r:rr,r>0);")
	    simplify)
	  (simplify-antecedent "with(r:rr,r>0);")
	  (simplify-antecedent "with(r:rr,r>0);")
	  (simplify-antecedent "with(r:rr,r>0);")
	  (simplify-antecedent "with(r:rr,r>0);")
	  (simplify-antecedent "with(r:rr,r>0);")
	  (simplify-antecedent "with(r:rr,r>0);")
	  (simplify-antecedent "with(r:rr,r>0);")
	  (simplify-antecedent "with(r:rr,r>0);"))
	simplify)
      simplify)
    (block 
      (script-comment "`direct-inference' at (1)")
      (antecedent-inference "with(p:prop,p);")
      (block 
	(script-comment "`antecedent-inference' at (0)")
	(force-substitution "x*y>0" "0<x*y" (0))
	(apply-macete-with-minor-premises 
	 strict-positivity-for-products-of-negatives)
	simplify)
      (block 
	(script-comment "`antecedent-inference' at (1)")
	(force-substitution "x*y>0" "0<x*y" (0))
	(block 
	  (script-comment "`force-substitution' at (0)")
	  (apply-macete-with-minor-premises 
	   strict-positivity-for-products)
	  direct-inference
	  (block 
	    (script-comment "`direct-inference' at (0)")
	    (antecedent-inference "with(p:prop,p);")
	    (incorporate-antecedent "with(x:rr,x>0);")
	    simplify)
	  (block 
	    (script-comment "`direct-inference' at (1)")
	    (antecedent-inference "with(p:prop,p and p);")
	    (incorporate-antecedent "with(y:rr,y>0);")
	    simplify))
	simplify))

    )))

(def-theorem bifurcate-product->=-inequality
  "forall(x,y:rr, x*y >= 0 
    iff 
   ((x <= 0 and y <= 0) or (x >= 0 and y >= 0)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises bifurcate-<=-inequality)
    (apply-macete-with-minor-premises bifurcate->=-inequality)
    (apply-macete-with-minor-premises bifurcate-product-equation)
    (apply-macete-with-minor-premises bifurcate-product->-inequality)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify

    )))

(def-compound-macete solve-product-equation-or-inequality
  (series
    reverse-zero-before-=
    reverse-zero-before-<
    reverse-zero-before-<=
    reverse-zero-before->
    reverse-zero-before->=
    bifurcate-product-equation
    bifurcate-product-<-inequality
    bifurcate-product-<=-inequality
    bifurcate-product->-inequality
    bifurcate-product->=-inequality
    ))

(def-theorem factor-quadratic-polynomial
  "forall(b,c,x:rr, 
     #(sqrt(b^2 - 4*c))
      implies 
     x^2 + b*x + c
      = 
     (x + (b - sqrt(b^2 - 4*c))/2)*(x + (b + sqrt(b^2 - 4*c))/2))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises sqrt-is-an-nth%root-special-case)
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises nth%root-power)
    simplify
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (incorporate-antecedent "with(p:prop,p);")
      (apply-macete-with-minor-premises defined-nth%root-is-nonnegative)
      simplify)

    )))

(def-compound-macete solve-quadratic-equation-or-inequality
  ;; Must be in form "x^2 + b*x + c OP 0" or "0 OP x^2 + b*x + c"
  ;; where OP is =, <, <=, >, or >=
  (series
   factor-quadratic-polynomial
   solve-product-equation-or-inequality))
   
