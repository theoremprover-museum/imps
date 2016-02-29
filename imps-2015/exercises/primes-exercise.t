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


(herald primes)

(def-constant divides
  "lambda(a,b:rr, #(b/a,zz))"
  (theory h-o-real-arithmetic))

(def-parse-syntax divides
  (left-method infix-operator-method)
  (binding 95))

(def-print-syntax divides
  (token " divides ")
  (method present-binary-infix-operator)
  (binding 95))

(def-theorem divisibility-lemma 
  "forall(a,b:zz, not(a=0) implies (a divides b iff forsome(k:zz, b = k*a)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant-globally divides)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("b/a"))
    simplify
    (backchain "with(r:rr,b:zz,b=r);")
    (weaken (0))
    simplify
    )))

(def-theorem divides-implies-le
  "forall(x,y:rr, 0<x and 0<y and x divides y implies x<=y)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant (0) divides)
    direct-and-antecedent-inference-strategy
    (force-substitution "x<=y" "0<=x*(y/x-1)" (0))
    (move-to-sibling 1)
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    simplify
    (cut-with-single-formula "0<y/x")
    simplify
    simplify
    (apply-macete-with-minor-premises positivity-of-inverse)

    )))


(def-constant positive%prime
  "lambda(m:zz, 1<m and forall(a:zz, 0<a and a divides m implies (a=1 or a=m)))"
  (theory h-o-real-arithmetic))

(def-constant no%factors%between
  "lambda(a,b:zz,c:rr, forall(k:zz, a<=k and k<=b implies not(k divides c)))"
  (theory h-o-real-arithmetic))

(def-theorem positive-prime-characterization
  "forall(m:zz,
     positive%prime(m)
       iff 
      (2<=m and no%factors%between(2,m-1,m)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    unfold-defined-constants
    direct-and-antecedent-inference-strategy-with-simplification
    (block
      (script-comment "The direction =>")
      (contrapose "with(p:prop,forall(a:zz,p));")
      (label-node before-instantiation)
      auto-instantiate-existential
      (jump-to-node before-instantiation)
      (for-nodes
       (unsupported-descendents)
       simplify))
    (block
      (script-comment "The direction <=")
      (auto-instantiate-universal-antecedent "with(m:zz,
  forall(k:zz,2<=k and k<=m-1 implies not(k divides m)));")
      simplify
      (label-node before-instantiation)
      (instantiate-theorem divides-implies-le ("a" "m"))
      (jump-to-node before-instantiation)
      (for-nodes
       (unsupported-descendents)
       simplify))
    )))

(def-theorem no-factors-recursion
  "forall(a,b:zz,theta:rr,
      a<=b
       implies 
      no%factors%between(a,b,theta)
       iff 
      (not(a divides theta) and no%factors%between(a+1,b,theta)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant-globally no%factors%between)
    direct-and-antecedent-inference-strategy-with-simplification
    (block (script-comment "Only case <= remains to be proved.")
	   (label-node before-case)
	   (case-split ("k=a"))
	   (jump-to-node before-case)
	   (for-nodes
	    (unsupported-descendents)
	    simplify))
    )))




(def-theorem no-factors-base
  "forall(a,b:zz,theta:rr, b<a implies (no%factors%between(a,b,theta) iff truth))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant (0) no%factors%between)
    simplify    
    )))


(def-compound-macete crude-primality-test
  (sequential
   positive-prime-characterization
   (repeat
    (without-minor-premises
     (series no-factors-recursion no-factors-base))
    divides-equation_h-o-real-arithmetic
    simplify)))

(def-theorem primes-exist
  "positive%prime(37)"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises crude-primality-test)
    )))

(def-theorem composites-exist
  "not(positive%prime(49))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises crude-primality-test)
    )))

;; For this one, the computation takes rather longer of course.
;; (A minute and a quarter on my IPX.)   

(def-theorem other-composites-exist
  "not(positive%prime(37^2))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises crude-primality-test)
    )))

;; This is a more demanding theorem, which is not worth proving in the
;; exercise.  

(def-theorem primality-test-refinement-lemma
  "forall(a,n:zz,
    1<=a and n<a^2 and a<=n-1
     implies 
    no%factors%between(2,a,n) iff no%factors%between(2,n-1,n))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (

    (let-script
     incorp-and-unfold 0
     ((incorporate-antecedent "with(n,k:zz,k divides n);")
      (unfold-single-defined-constant-globally divides)))
    (unfold-single-defined-constant-globally no%factors%between)
    direct-and-antecedent-inference-strategy
    (block (script-comment "first do the easy case: <=.")
	   (move-to-ancestor 5)
	   (move-to-descendent (1 0 0 0 0))
	   (backchain "with(p:prop,forall(k:zz,p));")
	   simplify)
    (block (script-comment "now the hard case: =>.")
	   (contrapose "with(p:prop,forall(k_$0:zz,p));")
	   (case-split ("k<=a"))
	   (block
	     (script-comment "Easy subcase: we use k.")
	     auto-instantiate-existential)
	   (block
	     (script-comment "Hard subcase: we need n/k.")
	     (instantiate-existential ("n/k"))
	     (move-to-ancestor 2)
	     (move-to-descendent (1))
	     (block
	       (script-comment "Justifying instantiation with n/k.")
	       $incorp-and-unfold)
	     (block
	       (script-comment "Show 2<=n/k.")
	       $incorp-and-unfold
	       direct-inference
	       (cut-with-single-formula "n/k<0 or n/k=0 or n/k=1 or 2<=n/k")
	       (antecedent-inference "with(p:prop,p or p or p or p);")
	       (script-comment "First three subcases are all the same. Last is trivial.")
	       (let-script
		contrapose-denom-remove 1
		;; The arg is the pattern to contrapose on
		;;
		((contrapose $1)
		 (apply-macete-with-minor-premises fractional-expression-manipulation)
		 simplify))
	       ($contrapose-denom-remove "with(r:rr,r<0);")
	       ($contrapose-denom-remove "with(r:rr,r=0);")
	       ($contrapose-denom-remove "with(r:rr,r=1);")
	       (script-comment "Now justify the cut on four cases.")
	       direct-and-antecedent-inference-strategy
	       simplify)
	     (block
	       (script-comment "Show n/k<=a.")
	       (apply-macete-with-minor-premises fractional-expression-manipulation)
	       (force-substitution "n<=a*k" "a*a<=a*k" (0))
	       (move-to-sibling 1)
	       (block (script-comment "Justify substitution.") simplify)
	       (apply-macete-with-minor-premises monotonicity-for-multiplication)
	       simplify)
	     (block
	       (script-comment "Show n/k divides a.")
	       (incorporate-antecedent "with(n,k:zz,k divides n);")
	       (unfold-single-defined-constant-globally divides)
	       (apply-macete-with-minor-premises fractional-expression-manipulation)
	       simplify)))
    )))

;; This proof is not at all hard, just mechanical, so do not bother with it in
;; the exercise.   

(def-theorem primality-test-refinement
  "forall(n:zz,
     positive%prime(n)
      iff 
     (n=2
      or 
     forsome(a:zz,
       1<=a and n<a^2 and a<=n-1 and no%factors%between(2,a,n))))"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    (apply-macete-with-minor-premises primality-test-refinement-lemma)
    (apply-macete-with-minor-premises positive-prime-characterization)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("n-1"))
    simplify
    simplify
    (cut-with-single-formula "3*n<=n^2")
    simplify
    (force-substitution "n^2" "n*n" (0))
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    simplify
    simplify
    simplify
    simplify
    (apply-macete-with-minor-premises no-factors-base)
    )))

;; Here's a slick computation of primality:

(def-theorem 3rd-mersenne-number-is-prime
  "positive%prime(2^2^3+1)"
  (theory h-o-real-arithmetic)
  (proof
   (
    simplify
    (apply-macete-with-minor-premises primality-test-refinement)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("17"))
    simplify
    simplify
    simplify
    (block 
      (let-macete no-factors-reduction
		  (repeat no-factors-recursion
			  no-factors-base
			  divides-equation_h-o-real-arithmetic
			  simplify))
      (apply-macete $no-factors-reduction))
    )))

;; and we can generalize it to a script that can be used to test primality: 

(def-script prime-test-script 1
  ;; The arg is an upper bound on the sqrt.
  (simplify
   (apply-macete-with-minor-premises primality-test-refinement)
   direct-and-antecedent-inference-strategy
   (label-node before-instantiation)
   (if (matches? "with(p:prop, forsome(a:zz, p))")
       (block
	 (instantiate-existential ($1))
	 (jump-to-node before-instantiation)
	 (for-nodes
	  (unsupported-descendents)
	  (block
	    simplify
	    (let-macete no-factors-reduction
			(repeat no-factors-recursion
				no-factors-base
				divides-equation_h-o-real-arithmetic
				simplify))
	    (apply-macete $no-factors-reduction))))
       (skip))))

;; Use the script to test some numbers:

"positive%prime(137)"

;; This one takes a minute and a half on my IPX
"positive%prime(983)" 


;; This example takes quite a long time (something like 15 minutes of 
;; computation).  But then, (2^(2^4))+1 = 65,537.

(def-theorem 4th-mersenne-number-is-prime
  "positive%prime(2^2^4+1)"
  (theory h-o-real-arithmetic)
  (proof
   (
    simplify
    (apply-macete-with-minor-premises primality-test-refinement)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("260"))
    simplify
    simplify
    simplify
    (block 
      (let-macete no-factors-reduction
		  (repeat no-factors-recursion
			  no-factors-base
			  divides-equation_h-o-real-arithmetic
			  simplify))
      (apply-macete $no-factors-reduction))
    )))



;; We turn next to a more elaborate use of the script mechanism for
;; computation.  We will search for a pair of twin primes (i.e.  primes that
;; differ by 2).

(def-constant prime%pair%between
  "lambda(a,b:zz, 
     forsome(i:zz, 
       a<=i and i+2<=b and positive%prime(i) and positive%prime(i+2)))"
  (theory h-o-real-arithmetic))

;; To carry out the search (after unfolding the definition of
;; prime%pair%between),  we will repeatedly instantiate the existential,
;; increasing the candidate by 2 each time.  

(def-script twin-prime-search 2
  ;; starting point (ODD) and sqrt of ending point 

  ((jump-to-node top-node)
   (instantiate-existential ($1))
   (jump-to-node top-node)
   (move-to-descendent (0 0))
   (for-nodes
    (node-and-siblings)
    (if (matches? ("positive%prime"))
	(block (weaken (* "with(p:prop, p)"))
	       (prime-test-script $2))
	simplify))
   (jump-to-node top-node)
   (twin-prime-search (% " ~a +2" $1) $2)))

;; And to start the search we unfold the definition and then label the top
;; node.  

(def-script twin-prime-start 2
  ;; starting point (ODD) and sqrt of ending point 
  (
   (unfold-single-defined-constant-globally prime%pair%between)
   (label-node top-node)
   (twin-prime-search $1 $2)))

"prime%pair%between(100,200)"

"prime%pair%between(102,200)"

;; Long search -- next pair is 137 and 139
;; This takes 2 minutes on triad (a sparc 10)
;; The derivation contains 246 sequent nodes when complete.
;;
"prime%pair%between(110,200)"

;; Of course the previous script has the drawback that it doesn't terminate if
;; there is no prime pair to be had in the interval.  Consider
;; "prime%pair%between(110,114)", where in fact there is no prime pair.  The
;; following pair of scripts overcomes this problem by keeing the upper bound
;; as parameter.  Guarding the recursive callis the test:
;;
;; (and (progresses?
;;	  (block (edit-and-post-sequent-node
;;		  ""
;;		  (% "(~a +2) <= ~a" $1 $3))
;;		 (jump-to-node newly-posted)))
;;	 (succeeds? simplify))
;;
;; This causes the assertion that x+2<=y to be placed in the deduction graph,
;; so to speak as a scratch node, where x is the current lower bound to the
;; search and y is the upper bound.  (jump-to-node newly-posted) transfers
;; attention to that new node, and the recursive call occurs only if
;; simplification can reduce it to truth.  

(def-script bounded-twin-prime-start 3
  ;; starting point (ODD), sqrt of ending point, and ending point 
  (
   (unfold-single-defined-constant-globally prime%pair%between)
   (label-node top-node)
   (bounded-twin-prime-search $1 $2 $3)))

(def-script bounded-twin-prime-search 3
  ;; starting point (ODD), sqrt of ending point, and ending point 
  ((jump-to-node top-node)
   (instantiate-existential ($1))
   (jump-to-node top-node)
   (move-to-descendent (0 0))
   (for-nodes
    (node-and-siblings)
    (if (matches? ("positive%prime"))
	(block (weaken (* "with(p:prop, p)"))
	       (prime-test-script $2))
	simplify))
   (jump-to-node top-node)(edit-and-post-sequent-node
		  ""
		  (% "(~a +2) <= ~a" $1 $3))
   (jump-to-node newly-posted)
   (if (succeeds? simplify)
       (block     
	 (bounded-twin-prime-search (% " ~a +2" $1) $2 $3))
       (skip))))

;; Try this script on "prime%pair%between(110,114)" and
;; "prime%pair%between(100,114)" to see it fail and succeed respectively.  

