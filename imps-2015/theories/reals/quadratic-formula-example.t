(include-files
 (files (imps theories/reals/polynomials)))

(comment

   Problem proposed by Zbig Dudek:

   Given

                x+1		     for x < 0
   dudek(x) =   (x-2)*(x-3) - 3      for x >= 0 & x < 4
                -1		     for x > 4

   prove the following:

   for x > 5 	dudek(x) < 0.

   for all x   	dudek(x) <= 1.

   for x > 1 	dudek(x) >= -3.25.

)

(def-constant dudek
  "lambda(x:rr,
     if(x < 0, x+1,
        x >= 0 and x <= 4, (x-2)*(x-3) - 3,
        x > 4, -1, 
        ?rr))"
  (theory h-o-real-arithmetic))

(def-theorem thm1
  "forall(x:rr, x > 5 implies dudek(x) < 0)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally dudek)
    simplify

    )))

(def-theorem thm2a
  "forsome(x:rr, dudek(x) > 1)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (instantiate-existential ("[1/3]"))
    (unfold-single-defined-constant-globally dudek)
    simplify

    )))

(def-theorem thm2b
  "forall(x:rr, dudek(x) <=3)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally dudek)
    (raise-conditional (0))
    (raise-conditional (0))
    simplify
    direct-and-antecedent-inference-strategy
    (force-substitution "x^2<=5*x" "x^2+(-5)*x+0<=0" (0))
    (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises 
       solve-quadratic-equation-or-inequality)
      (cut-with-single-formula "nth%root(2,25)=5")
      simplify
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises 
	 iota-free-characterization-of-nth%root)
	simplify))
    (block 
      (script-comment "`force-substitution' at (1)") 
      (weaken (1 0)) 
      simplify)

    )))

(def-theorem thm3
  "forall(x:rr, x > 1 implies dudek(x) >= -(3+[25/100]))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally dudek)
    (raise-conditional (0))
    (raise-conditional (0))
    simplify
    direct-and-antecedent-inference-strategy
    (force-substitution 
     "5*x<=[25/4]+x^2" 
     "0<=x^2 +(-5)*x + [25/4]" (0))
    (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises 
       solve-quadratic-equation-or-inequality)
      simplify)
    (block 
      (script-comment "`force-substitution' at (1)") 
      (weaken (1 0)) 
      simplify)

    )))

