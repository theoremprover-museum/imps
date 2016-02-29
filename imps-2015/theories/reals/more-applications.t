(include-files
 (files (imps theories/partial-orders/applications)
	(imps theories/reals/exponentiation)
	))

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

