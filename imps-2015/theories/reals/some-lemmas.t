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


(herald SOME-LEMMAS)

(def-theorem nn-addition-rewrite 
  "forall(x,y:zz, #(x+y,nn) iff 0<=x+y)"
  (theory h-o-real-arithmetic)
  (usages  rewrite)
  (proof (direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises nn-in-quasi-sort_h-o-real-arithmetic)
	  (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
	  simplify)))

(def-theorem ()
  "forall(x,y:nn,#(x+y,nn ))"
  (theory  h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    ))
  (usages d-r-convergence))

(def-theorem ()
  "forall(x,y:nn,  #(x*y,nn ))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    (apply-macete-with-minor-premises positivity-for-products)
    simplify
    ))
  (usages d-r-convergence))

(def-theorem ()
  "forall(x,y:ind,#(x,nn) and #(y,nn) and y<=x implies #(x-y,nn ))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    ))
  (usages d-r-convergence))

(def-theorem ()
  "forall(x,y:ind,#(x,nn) and #(y,nn) and 1<=y implies #(x^y,nn ))"
  (theory h-o-real-arithmetic)

  (proof
   (
    (cut-with-single-formula "forall(x,y:zz,1<=y and 0<=x implies #(x^y,zz) and 0<=x^y)")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    (instantiate-universal-antecedent "forall(x,y:zz,1<=y and 0<=x implies #(x^y,zz) and 0<=x^y);" ("x" "y"))
    (contrapose "with(x:ind,not(0<=x));")
    simplify
    beta-reduce-repeatedly
    (induction integer-inductor ("y"))
    (force-substitution "x^(1+t)" "x^t*x" (0 1))
    direct-inference
    simplify
    (apply-macete-with-minor-premises positivity-for-products)
    direct-and-antecedent-inference-strategy
    simplify


;;;    (cut-with-single-formula "forall(x,y:zz,1<=y and 0<=x implies #(x^y,zz) and 0<=x^y)")
;;;    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
;;;    direct-and-antecedent-inference-strategy
;;;    simplify
;;;    (induction integer-inductor ("y"))
;;;    (force-substitution "x^(1+t)" "x^t*x" (0))
;;;    (apply-macete-with-minor-premises positivity-for-products)
;;;    simplify
;;;    simplify




    ))
  (usages d-r-convergence))

(def-theorem ()
  "forall(j:zz, 0<=j implies #(j,nn))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify

    ))
  (usages d-r-convergence))

(def-theorem ()
  "forall(x:rr, 0<=x and #(x,zz) implies #(x,nn))"
  (theory h-o-real-arithmetic)
  (proof

   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    beta-reduce-repeatedly

    ))
  (usages d-r-convergence))

(def-theorem () 
  "forall(n:nn,#(n+[-1],nn) iff 0<n)"
  (theory h-o-real-arithmetic)
  (proof

   (
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    direct-and-antecedent-inference-strategy
    simplify
    simplify

    ))

  (usages rewrite))

(def-theorem ()
  "forall(x:rr, #(abs(x)))"
  (theory h-o-real-arithmetic)
  (proof

   (
    (unfold-single-defined-constant (0) abs)
    insistent-direct-inference
    beta-reduce-repeatedly
    ))
  (usages d-r-convergence))

(def-theorem ()
  "forall(x,y:rr, #(max(x,y)))"
  (theory h-o-real-arithmetic)

  (proof

   (
    unfold-defined-constants
    insistent-direct-inference
    beta-reduce-repeatedly
    ))
  (usages d-r-convergence))

(def-theorem positivity-for-squares
  "forall(x:rr, 0<=x^2)"
  (theory h-o-real-arithmetic)

  (proof
   (
    direct-and-antecedent-inference-strategy
    (force-substitution "x^2" "x*x" (0))
    (cut-with-single-formula "0<=x or 0<=[-1]*x")
    (antecedent-inference "with(x:rr,0<=x or 0<=[-1]*x);")
    (apply-macete-with-minor-premises positivity-for-products)
    (force-substitution "x*x" "([-1]*x)*([-1]*x)" (0))
    (apply-macete-with-minor-premises positivity-for-products)
    simplify
    simplify
    simplify
    )))

(def-theorem triangle-inequality
  "forall(x,y:rr,abs(x+y)<=abs(x)+abs(y))"
  (theory h-o-real-arithmetic)
  (proof

   (
    unfold-defined-constants
    (prove-by-logic-and-simplification 3)

    )))

(def-theorem non-negativity-of-absolute-value
  "forall(x:rr,0<=abs(x))"
  (theory h-o-real-arithmetic)
  (proof

   (
    unfold-defined-constants
    (prove-by-logic-and-simplification 3)
    )))

(def-theorem min-definedness
  "forall(x,y:rr,#(min(x,y)))"
  (theory h-o-real-arithmetic)
  (proof

   (
    unfold-defined-constants
    insistent-direct-inference
    beta-reduce-repeatedly

    ))
  (usages d-r-convergence))

(def-theorem maximum-1st-arg
  "forall(x,y:rr,x<=max(x,y))"
  (theory h-o-real-arithmetic)
  (proof
   (
    unfold-defined-constants
    (prove-by-logic-and-simplification 3)
    )
   ))

(def-theorem maximum-2nd-arg
  "forall(x,y:rr,y<=max(x,y))"
  (theory h-o-real-arithmetic)
  (proof
   (
    unfold-defined-constants
    (prove-by-logic-and-simplification 3)
    )
   ))

(def-theorem minimum-1st-arg
  "forall(x,y:rr,min(x,y)<=x)"
  (theory h-o-real-arithmetic)
  (proof
   (
    unfold-defined-constants
    (prove-by-logic-and-simplification 3)
    )
   ))

(def-theorem minimum-2nd-arg
  "forall(x,y:rr,min(x,y)<=y)"
  (theory h-o-real-arithmetic)
  (proof
   (
    unfold-defined-constants
    (prove-by-logic-and-simplification 3)
    )
   ))

(def-theorem min-lemma
  "forall(a,b,c:rr, a<b and a<c implies forsome(d:rr, a<d and d<=b and d<=c))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-existential ("min(b,c)"))
    (unfold-single-defined-constant-globally min)
    (case-split ("b<=c"))
    simplify
    simplify
    (apply-macete-with-minor-premises minimum-1st-arg)
    (apply-macete-with-minor-premises minimum-2nd-arg)
    )))


(def-theorem max-lemma
  "forall(a,b,c:rr, b<a and c<a implies forsome(d:rr, d<a and b<=d and c<=d))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-existential ("max(b,c)"))
    (unfold-single-defined-constant-globally max)
    (case-split ("b<=c"))
    simplify
    simplify
    (apply-macete-with-minor-premises maximum-1st-arg)
    (apply-macete-with-minor-premises maximum-2nd-arg)
    )))
