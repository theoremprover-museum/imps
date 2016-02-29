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


;
;
;			  CALCULUS EXERCISE
;
;
; The following file defines a simple extension of the theory
; h-o-real-arithmetic, which provides an algebraic, axiomatic
; characterization of the derivative operator for polynomials. No
; epsilon/delta arguments are necessary.
;
; To do this exercise, have the "tea" process evaluate each
; s-expression in the file in the order in which they appear.  To
; evaluate an s-expression, position the cursor somewhere within the
; s-expression and select "Evaluate def-form" from the "Def-forms"
; menu.  This operation may also be directly invoked with the the
; keystroke "C-c e".  Note that some forms take a few seconds to
; evaluate.
;
; If a form begins with "def-theorem" you will want to PROVE it first
; before asking IMPS to install it as a theorem.
;
; If you would like to make additions to this file, just make a copy
; of it and put it in your "imps/theories" directory or someplace
; else.
;
;
; PART I: Build the Theory
;
;
; Before we can start, we need to load into IMPS some basic
; mathematics including the theory h-o-real-arithmetic, so load the
; section of the theory library called FOUNDATION by evaluating

(load-section foundation)

; The next step is to create a language consisting of the language of
; the theory h-o-real-arithmetic plus a new constant "d" to serve as a
; derivative operator.  The sort of d is "[[rr -> rr] -> [rr -> rr]]";
; hence, d transforms one real-valued function into another.  Since
; there is no distinction between upper-case and lower-case, we write
; "d" as "D" for readability.

(def-language calculus-language
  (embedded-language h-o-real-arithmetic)
  (constants				
   (d "[[rr -> rr],[rr -> rr]]")))

; The following def-theory form creates an extension of the theory
; h-o-real-arithmetic in which D is axiomatized by five axioms.

(def-theory calculus-theory
  (language calculus-language)
  (component-theories h-o-real-arithmetic)
  (axioms
   (definedness-of-differentiable-fns
    ;;
    ;; If the derivative is defined at a point,
    ;; then so is the function (at that point).
    ;; 
    "forall(x:rr,f:[rr -> rr], #(D(f)(x)) implies #(f(x)))")			
   (sum-rule
    ;;
    ;; If the derivatives are defined at a point, then
    ;; the derivative of the SUM (at that point)
    ;; is the SUM of the derivatives (at that point).
    ;; 
    "forall(f,g:[rr -> rr],x:rr,
       #(D(f)(x)) and #(D(g)(x))
        implies
       D(lambda(x:rr,f(x)+g(x)))(x) = D(f)(x)+D(g)(x))")
   (product-rule
    ;;
    ;; If the derivatives are defined at a point, then
    ;; the derivative of the PRODUCT (at that point)
    ;; is a certain sum of products (at that point).
    ;; 
    "forall(f,g:[rr -> rr],x:rr,
       #(D(f)(x)) and #(D(g)(x))
        implies
       D(lambda(x:rr,f(x)*g(x)))(x) = D(f)(x)*g(x) + f(x)*D(g)(x))")
   (diff-constant
    ;;
    ;; The derivative of a constant function
    ;; is the function that is constantly zero.
    ;; 
    "forall(c:rr, D(lambda(x:rr,c)) = lambda(z:rr,0))")
   (diff-identity
    ;;
    ;; The derivative of the identity function
    ;; is the function that is constantly one.  
    ;;
    "D(lambda(x:rr,x)) = lambda(x:rr,1)")))

; The next form tells IMPS to print "d" in calligraphic font with TeX.

(def-print-syntax d
 tex
 (token " {\\cal D} ")
 (method present-tex-prefix-operator)
 (binding 160))

; To set the current theory to "calculus-theory" using the mouse, go
; to the "General" menu and click on the option "Set current theory",
; or else evaluate the following form:

(set (current-theory) (name->theory 'calculus-theory))


; PART II: Prove the Homogeneity of Differentiation
;
; The homogeneity of differentiation -- the fact that we can shift a
; constant factor out past the derivative operator -- follows from the
; product rule.  We'll prove it.
;
; A word of caution:
;
; In this (and other proofs) you will need to "lambda-abstract" a term
; in order to apply the rules for differentiation.  Thus, think of "c"
; as "lambda(x:rr,c)(x)".  For the following exercise, do it directly
; using force substitution.  Below you will learn how to get IMPS to
; do this abstraction using macetes.
;
; To start the proof, go to the "DG" menu and click on "Start dg".
; Alternatively, you can click on the "Start a new deduction" icon.
; IMPS will then prompt you for a formula in the minibuffer.  In the
; minibuffer, type in the string of characters between the double
; quotes.

(view-expr 
 "forall(x,c:rr,f:[rr -> rr],
    #(D(f)(x)) implies D(lambda(x:rr,c*f(x)))(x) = c*D(f)(x))")

; or click the RIGHT mouse button on the formula, BETWEEN THE DOUBLE
; QUOTES, and then press <RETURN>.
;
; In order to prove the theorem you will have to do the following:
;
; 1. Find force-substitution on the command menu.  You want to lambda
; abstract "c" to the form "lambda(x:rr,c)(x)" at c's leftmost (0-th)
; occurrence.  This will leave you with two subgoals: showing that the
; result of making the substitution is true, and showing that the
; substitution is legitimate.
;
; 2. To justify the substitution, select either simplify or
; beta-reduce on the "Commands" submenu of the "Extend-DG" menu.  The
; keystroke "C-c s" will also cause IMPS to simplify.
;
; 3. Moving back to the main subgoal, look for the product rule on the
; "Macetes" submenu of the "Extend-DG" menu.  This will also add two
; subgoals: one in which the product rule has been applied, and one
; requiring that the derivative of lambda(x:rr,c) be defined at x.
;
; 4. To knock off the definedness requirement, find diff-constant on
; the "Macetes" submenu; then either simplify or beta-reduce as above.
;
; 5. Moving back to the main subgoal, you will again need
; diff-constant.  Simplify and, finally, you need to use definedness
; of differentiable functions from the "Macetes" submenu.
;
; After you have proved the theorem, install it by evaluating the
; following form:

;;(!) 
;Prove:

(def-theorem homogeneity-of-diff
  "forall(x,c:rr,f:[rr -> rr],
     #(D(f)(x)) implies D(lambda(x:rr,c*f(x)))(x) = c*D(f)(x))"
  (theory calculus-theory)
  (proof 
   (

    (force-substitution "c" "lambda(x:rr,c)(x)" (0))
    (apply-macete-with-minor-premises product-rule)
    (apply-macete-with-minor-premises diff-constant)
    simplify
    (apply-macete-with-minor-premises definedness-of-differentiable-fns)
    (apply-macete-with-minor-premises diff-constant)
    beta-reduce-repeatedly

    )))


; PART III: Prove the Power Rule
;
; Next we will prove the power rule -- that the derivative of x^n is
; n*x^(n-1) -- using induction of n.

(view-expr 
 "forall(n:zz, 
    2<=n implies D(lambda(x:rr,x^n)) = lambda(x:rr,n*x^(n-1)))")

; In the formulation, we assume that 2<=n.  This is because the IMPS
; theory of the reals does not define 0^0.  As a consequence, the
; power rule is false for n=1, as D(lambda(x:rr,x^1)) is constantly 1,
; while lambda(x:rr,1*x^0) is constantly 1, except at 0, where it is
; undefined.  The power rule as formulated here is correct (in our
; theory of the reals, for the usual derivative) for n=0, but this
; fact cannot be proved from the purely algebraic properties given in
; the axiomatization above.
;
; To prove the power rule, first observe that it asserts the equality
; of two functions.  By contrast, the axioms governing D talk about
; the values of the functions.  Thus, we will need to use the
; extensionality principle to reduce the assertion to the claim that
; the functions behave the same for all arguments.
;
; We will describe the proof in less detail than the previous one.
;
; 1. Use direct inferences to break up the assertion.
;
; 2. Cut with the formula 
; "forall(z:rr, d(lambda(x:rr,x^n))(z) = lambda(x:rr,n*x^(n-1))(z))"
;
; 3. Apply extensionality to the main subgoal.
;
; 4. Apply induction (with integer inductor) to the subgoal justifying
; the application of cut.
;
; 5. In the base case, replace x^2 with
; lambda(x:rr,x)(x)*lambda(x:rr,x)(x), followed by the product rule,
; diff-identity, and simplification.
;
; 6. In the induction step, replace x^(1+t) by
; lambda(x:rr,x^t)(x)*lambda(x:rr,x)(x), followed by the product rule,
; diff-identity, and simplification.
;
; After you have proved the power rule, install it by evaluating the
; following form:

;;(!)

(def-theorem power-rule
  "forall(n:zz,2<=n implies D(lambda(x:rr,x^n)) = lambda(x:rr,n*x^(n-1)))"
  (theory calculus-theory)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula 
     "forall(z:rr, d(lambda(x:rr,x^n))(z) = lambda(x:rr,n*x^(n-1))(z))")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     extensionality
     simplify)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (induction integer-inductor ("n"))
     (block 
      (script-comment "`induction' at (0 0 0 0 0)")
      (force-substitution 
       "x^2"
       "lambda(x:rr,x)(x)*lambda(x:rr,x)(x)"
       (0))
      (block 
       (script-comment "`force-substitution' at (0)")
       (apply-macete-with-minor-premises product-rule)
       (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
	(apply-macete-with-minor-premises diff-identity)
	simplify)
       (apply-macete-with-minor-premises diff-identity))
      simplify)
     (block 
      (script-comment "`induction' at (0 0 0 1 0 0 0 0 0)")
      (force-substitution 
       "x^(1+t)"
       "lambda(x:rr,x^t)(x)*lambda(x:rr,x)(x)"
       (0))
      (block 
       (script-comment "`force-substitution' at (0)")
       (apply-macete-with-minor-premises product-rule)
       (apply-macete-with-minor-premises diff-identity)
       simplify)
      simplify))

    )))

; Optional Problem  
;
; You may want to try the generalized power rule, about the derivative
; of f(x)^n.  The proof is similar, except that you will have to take
; cases (using the command case-split) on whether #(f(x)) at a couple
; points in the proof.  You will also need to use "eta-reduction" to
; reduce lambda(x:rr,f(x)) to f a few times.  You will find it in the
; macete menu under the name tr%unary-eta-reduction (it is
; "transportable" to any logical theory, but handles only "unary" or
; one-place functions).

;;(!)

(def-theorem generalized-power-rule
  "forall(n:zz,f:[rr -> rr], x:rr, 
     #(D(f)(x)) and 2<=n 
      implies 
     D(lambda(x:rr,f(x)^n))(x) = n*f(x)^(n-1)*D(f)(x))"
  (theory calculus-theory)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (induction integer-inductor ("n"))
    (force-substitution 
     "f(x)^2" 
     "lambda(x:rr,f(x))(x)*lambda(x:rr,f(x))(x)" 
     (0))
    (apply-macete-with-minor-premises product-rule)
    (apply-macete-with-minor-premises tr%unary-eta-reduction)
    (cut-with-single-formula "#(f(x))")
    simplify
    (apply-macete-with-minor-premises definedness-of-differentiable-fns)
    (apply-macete-with-minor-premises tr%unary-eta-reduction)
    (case-split ("#(f(x))"))
    simplify
    simplify
    (force-substitution "f(x)^(1+t)" "f(x)^t*f(x)" (0))
    (force-substitution "f(x)^t" "lambda(x:rr,f(x)^t)(x)" (0))
    (apply-macete-with-minor-premises product-rule)
    beta-reduce-repeatedly
    simplify
    simplify
    (case-split ("#(f(x))"))
    simplify
    simplify

    )))


; PART IV: Build a Macete for Symbolic Differentiation
;
; The remainder of this exercise is devoted to showing how to use
; macetes to carry out symbolic computations.  In particular, we will
; build a macete to perform symbolic differentiation of polynomials.
;
; We first introduce a pair of "non-directional, schematic" macetes.
; They use matching and substitution procedures which do not respect
; the normal scoping rules for binding operators.  Hence, the result
; is not necessarily logically related to the argument.  How can such
; a macete possibly be useful?  See below.

(def-schematic-macete abstraction-for-diff-sum
  "with(a,b:rr,y:rr,
     D(lambda(x:rr,a+b))(y) =
     D(lambda(x:rr,lambda(x:rr,a)(x)+lambda(x:rr,b)(x)))(y))"
  ;; 
  ;; non-directional:
  null
  (theory calculus-theory))

(def-schematic-macete abstraction-for-diff-prod
  "with(a,b:rr,y:rr,
     D(lambda(x:rr,a*b))(y) =
     D(lambda(x:rr,lambda(x:rr,a)(x)*lambda(x:rr,b)(x)))(y))"
  ;; 
  ;; non-directional:
  null					
  (theory calculus-theory))

; Given a context C and an expression E_0, the macetes
;
; ABSTRACTION-FOR-DIFF-PROD
; ABSTRACTION-FOR-DIFF-SUM
;
; applied in series construct an "abstracted expression" E_1.
;
; To make this logically safe, we supply a pair of macetes that ARE
; guaranteed to preserve value: They serve as "checks".  One is
; applied to E_0, and the other is E_1.  If the results are equal,
; then we have validated that E_0 = E_1.  Hence, in this case, the safe
; macete can return E_1; otherwise, it returns E_0, which is certainly
; safe.
;
; For these two macetes, the checks are simply to beta-reduce repeatedly.  

(def-compound-macete abstraction-for-diff-safe
  (sound
   (series abstraction-for-diff-prod abstraction-for-diff-sum)
   beta-reduce-repeatedly
   beta-reduce-repeatedly))

; We next define a macete that performs symbolic differentiation by
; repeatedly applying the differentiation we proved above:

(def-compound-macete calculus-rules
  (series
    (repeat
     diff-constant
     diff-identity
     power-rule
     sum-rule
     product-rule
     abstraction-for-diff-safe
     sum-rule
     product-rule)
    simplify
    definedness-of-differentiable-fns))

; Example: compute the value of

(view-expr "with(y:rr, y = D(lambda(x:rr,6*x^3+7*x+5))(12))")

; by starting a deduction with this formula as the goal.
;
; Apply the macete "calculus-rules". This should produce new subgoals:
;
; a. One of the goals is "with(y:rr, y = SOME-NUMBER)" where SOME-NUMBER
;    stands for a numeral.
;
; b. The remaining goals are definedness assertions which can
;    themselves be knocked off with "calculus-rules".
;
; Note that we are NOT trying to prove that any y:rr has the same
; value as D(lambda(x:rr,6*x^3+7*x+5))(12).  Rather, we are REDUCING
; the assertion that y = D(lambda(x:rr,6*x^3+7*x+5))(12) to the
; assertion that y = SOME-NUMBER.


; PART V: Optional Exercise
; 
; The following exercise is somewhat more difficult than the preceding
; ones.  Prove:

;;(!)
(def-theorem differentiation-of-polynomials
  "forall(n:zz,a:[zz -> rr],
     1<=n and forall(j:zz,1<=j and j<=n implies #(a(j))) 
      implies 
     D(lambda(z:rr,sum(1,n,lambda(j:zz,a(j)*z^j)))) =
     lambda(z:rr,a(1)+sum(2,n,lambda(j:zz,j*a(j)*z^(j-1)))))"
  (theory calculus-theory)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula 
     "with(a:[zz -> rr],n:zz,
        forall(z:rr,
          D(lambda(z:rr,sum(1,n,lambda(j:zz,a(j)*z^j))))(z) =
          lambda(z:rr,a(1)+sum(2,n,lambda(j:zz,j*a(j)*z^(j-1))))(z)))")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      extensionality
      simplify)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (induction integer-inductor ("n"))
      (block 
	(script-comment "`induction' at (0 0 0 0 0 0 0 0 0)")
	(apply-macete-with-minor-premises calculus-rules)
	(apply-macete-with-minor-premises calculus-rules)
	(apply-macete-with-minor-premises calculus-rules))
      (block 
	(script-comment "`induction' at (0 0 0 0 1 0 0 0 0 0 0 0 0)")
	(apply-macete-with-minor-premises calculus-rules)
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (0)")
	  (backchain "with(p:prop,p implies p);")
	  direct-and-antecedent-inference-strategy
	  simplify)
	simplify
	simplify
	(apply-macete-with-minor-premises calculus-rules)
	(apply-macete-with-minor-premises calculus-rules)
	(apply-macete-with-minor-premises calculus-rules)
	(apply-macete-with-minor-premises calculus-rules)))

    )))

;
; 			   END OF EXERCISE




