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


(herald contraction)
;

;	    BANACH CONTRACTIVE MAPPING FIXED POINT THEOREM
;
;
;
; This file contains an outline for producing an IMPS proof of the
; following fixed point theorem due to Banach:
; 
;    THEOREM.  A contractive mapping on a complete metric space has a
;    fixed point.
; 
;
; 
; PART I: Metric Space Machinery
; 
; The first step is to load some basic machinery for reasoning about
; metric spaces which is contained in the following files.

; (*require nil '(metric_spaces metric-spaces) imps-implementation-env)
; (*require nil '(metric_spaces metric-space-pairs) imps-implementation-env)
; (*require nil '(metric_spaces metric-space-supplements) imps-implementation-env)
(load-section metric-space-pairs)

;;(*require nil '(metric_spaces metric-space-pairs-supplements) imps-implementation-env)


; PART II: Facts about Powers and Geometric Series

; The following results are proved in the theory named
; h-o-real-arithmetic, which is essentially a theory of complete ordered
; fields.

;(set (current-theory) (name->theory 'h-o-real-arithmetic))

(def-theorem boundedness-for-r^n	
  "forall(r:rr,n:zz, 
     0<r and r<1 and 1<=n 
      implies 
     0<r^n and r^n<r^(n-1) and r^n<1)"
  (theory h-o-real-arithmetic)

  ;; Apply induction command with integer-inductor. Then apply the
  ;; macete exp-out *without* minor premises (use special command
  ;; menu).  Finally use the command simplify.

  (proof ((induction integer-inductor ("n"))
	  (apply-macete exp-out)
	  simplify)))

;;
;; (set (proof-log-port) (standard-output))
;; 

(def-theorem  monotonicity-for-r^n
  "forall(r:rr,n:zz,0<r and r<1 and 1<=n implies r^n<r^(n-1))"
  (theory h-o-real-arithmetic)

  ;; Use the command direct-and-antecedent-inference-strategy.
  ;; Then instantiate the theorem boundedness-for-r^n with r and n
  ;; (the same names as the bound variables).

  (proof (direct-and-antecedent-inference-strategy
	  (instantiate-theorem boundedness-for-r^n ("r" "n")))))

(def-theorem  boundedness-by-1-for-r^n
  "forall(r:rr,n:zz,0<r and r<1 and 1<=n implies r^n<1)"
  (theory h-o-real-arithmetic)
  
  ;; Same commands as before: Direct-and-antecedent-inference 
  ;; strategy, then instantiate-theorem with boundedness-for-r^n.

  (proof (direct-and-antecedent-inference-strategy
	  (instantiate-theorem boundedness-for-r^n ("r" "n")))))

(def-compound-macete simple-arithmetic-expression-manipulator
  (sequential
   (repeat
    positivity-for-r^n
    fractional-expression-manipulation)
   simplify))

(comment   "forall(r:rr,p,q:zz, 
     0<=p and p<=q and not(r=0) 
      implies 
     sum(p,q,lambda(j:zz,r^j))=r^p*(1-r^(q-p+1))/(1-r))" )

(comment   "forall(r:rr,p,q:zz, 
     0<=p and p<=q and not(r=0) and not(r=1) 
      implies 
     sum(p,q,lambda(j:zz,r^j))=r^p*(1-r^(q-p+1))/(1-r))" )

;;(!)
(def-theorem geometric-series-formula
  "forall(a,r:rr,p,q:zz, 
     0<=p and p<=q and not(r=0) and not(r=1) 
      implies 
     sum(p,q,lambda(j:zz,r^j*a))=a*r^p/(1-r)*(1-r^(q-p+1)))"
  (theory h-o-real-arithmetic)

  ;; Apply macete fractional-expression-manipulation.  Then apply
  ;; command induction with the integer-inductor; specify q as
  ;; variable of induction. This induction will run for a minute
  ;; and a half, but it completes the proof.  

  (proof ((apply-macete-with-minor-premises fractional-expression-manipulation)
	  (induction integer-inductor ("q")))))

(def-theorem upper-estimate-geometric-series-lemma
  "forall(a,r:rr,p,q:zz, 
     1<=p and p<=q and 0<r and r<1 and 0<a 
      implies 
     a*r^p/(1-r)*(1-r^(q-p+1)) <a*r^p/(1-r))"
  (theory h-o-real-arithmetic)

  ;; Apply macete fractional-expression-manipulation, simplify, and.
  ;; then apply macete positivity-for-r^n. Finish with 
  ;; direct-and-antecedent-inference-strategy.

  (proof ((apply-macete-with-minor-premises fractional-expression-manipulation)
	  simplify
	  (apply-macete-with-minor-premises positivity-for-r^n)
	  direct-and-antecedent-inference-strategy)))



(def-theorem  geometric-series-upper-estimate
  "forall(a,r:rr,p,q:zz, 
     1<=p and p<=q and 0<r and r<1 and 0<a 
      implies 
     sum(p,q,lambda(j:zz,r^j*a))<a*r^p/(1-r))"
  (theory h-o-real-arithmetic)

  ;; Apply macete geometric-series-formula, and then apply macete
  ;; upper-estimate-geometric-series-lemma.

  (proof ((apply-macete-with-minor-premises geometric-series-formula)
	  (apply-macete-with-minor-premises upper-estimate-geometric-series-lemma))))

(def-theorem powers-corollary
  "forall(r,eps:rr,
     0<r and r<1 and 0<eps 
      implies 
     forsome(n:zz, 1<=n and r^n<eps))"
  (theory h-o-real-arithmetic)

  ;; We already have the theorem (called r^n-convergent-to-infinity)
  ;; that s^n --> oo provided s>1.  Thus (r^[-1])^n --> oo if r<1.
  ;; From this will follow s^n --> 0 for 0<r<1, which is essentially
  ;; the content of the corollary.

  ;; 1. Use direct-and-antecedent-inference-strategy.
  ;; 2.	Instantiate the theorem r^n-convergent-to-infinity with
  ;;    r^[-1].  There will be two subgoals.
  ;; 3. To knock off the first, contrapose the assumption not(1<r^[-1]),
  ;;    then use the macete simple-arithmetic-expression-manipulator.
  ;; 4. Turning to the main case, use incorporate-antecedent on
  ;;    convergent%to%infinity(lambda(n:zz,(r^[-1])^n)), so as to be 
  ;;    able to unfold the definition of convergent%to%infinity, and 
  ;;    then use direct-and-antecedent-inference-strategy.
  ;; 5. Instantiate universal antecedent with eps^[-1]+1 for m. (The
  ;;    +1 is needed because the assumption is a weak inequality while
  ;;    the assertion has a strict one.)
  ;; 6. Instantiate universal antecedent with a sufficiently large
  ;;    integer. It suffices to use max(1,x).  There will be two 
  ;;    subgoals. To knock off the first, contrapose on 
  ;;    not(x<=max(1,x)), and then use macete maximum-2nd-arg.
  ;; 7.	Turning to the main case, add eps^[-1]<(r^[-1])^max(1,x) using
  ;;    cut-with-single-formula.  To discharge this cut formula, just 
  ;;    simplify on it. 	 
  ;; 8. Instantiate existential with max(1,x).  Knock off the easy 
  ;;    subgoal using macete maximum-1st-arg.
  ;; 9. Apply incorporate-antecedent to the assumption 
  ;;    eps^[-1]<(r^[-1])^max(1,x), and then use the macete 
  ;;    simple-arithmetic-expression-manipulator, finishing by applying 
  ;;    the macete positivity-for-r^n.  

  (proof
   (direct-and-antecedent-inference-strategy
    (instantiate-theorem r^n-convergent-to-infinity ("r^[-1]"))
    (contrapose "with(r:rr,not(1<r^[-1]));")
    (apply-macete-with-minor-premises simple-arithmetic-expression-manipulator)
    (incorporate-antecedent "with(r:rr,convergent%to%infinity(lambda(n:zz,(r^[-1])^n)));")
    (unfold-single-defined-constant (0) convergent%to%infinity)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(r:rr,
  forall(m:rr,
    forsome(x:zz,forall(j:zz,x<=j implies m<=(r^[-1])^j))));" ("eps^[-1]+1"))
    (instantiate-universal-antecedent "with(r,eps:rr,x:zz,
  forall(j:zz,x<=j implies eps^[-1]+1<=(r^[-1])^j));" ("max (1,x)"))
    (contrapose "with(x:zz,not(x<=max(1,x)));")
    (apply-macete-with-minor-premises maximum-1st-arg)
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (cut-with-single-formula "eps^[-1]<(r^[-1])^max(1,x)")
    (instantiate-existential ("max (1,x)"))
    (apply-macete-with-minor-premises maximum-1st-arg)
    (incorporate-antecedent "with(x:zz,r,eps:rr,eps^[-1]<(r^[-1])^max(1,x));")
    (apply-macete-with-minor-premises simple-arithmetic-expression-manipulator)
    (apply-macete-with-minor-premises positivity-for-r^n)
    simplify)))


; PART III: Facts about Function Iteration
; 
; Given a mapping f:[ind_1,ind_1] and x:ind_1, we want to define 
; the sequence of iterates x, f(x), f(f(x)),....  (ind_1 is an
; unspecified abstract domain.)  This suggests we define by 
; recursion a function on the integers having f,x as parameters.

(set (current-theory) (name->theory 'generic-theory-1))

(def-recursive-constant iterate
  "lambda(iter:[zz,ind_1], f:[ind_1,ind_1],x:ind_1,
     lambda(n:zz, if(n=0,x,f(iter(n-1)))))"
  (theory generic-theory-1)
  (definition-name iterate))

(def-theorem iterate-definedness
  "forall(f:[ind_1,ind_1],x:ind_1,z:zz, 
     total_q{f,[ind_1,ind_1]} and 0<=z implies #(iterate(f,x)(z)))"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof 

   (
    (induction integer-inductor ())

    )))

(def-theorem undefined-for-negative
  "forall(n:zz,x:ind_1,f:[ind_1,ind_1],
     n<0 implies not(#(iterate(f,x)(n))))"
  (theory generic-theory-1)
  (usages transportable-macete)

  ;; Use Direct-and-antecedent-inference-strategy.  Show that 
  ;; 
  ;;    iterate(f,x) = lambda(n:zz,if(n<0,?ind_1,iterate(f,x)(n)))
  ;;
  ;; by:
  ;;   a. Instantiating the theorem iterate-minimality_generic-theory-1 
  ;;      with f and x.
  ;;   b. Instantiating the universal antecedent with 
  ;;      lambda(n:zz,if(n<0,?ind_1,iterate(f,x)(n))).
  ;; There are two remaining subgoals.  For the first: contrapose,
  ;; apply command extensionality, do direct-inference, unfold first
  ;; occurrence of iterate, take cases on sign of x_0, and simplify.
  ;; For the second, backchain, and then simplify.

  (proof 
   (

    direct-and-antecedent-inference-strategy
    (instantiate-theorem iterate-minimality_generic-theory-1 ("f" "x"))
    (instantiate-universal-antecedent
     "with(p:prop,forall(h_0:[zz,ind_1],p));"
     ("lambda(n:zz,if(n<0,?ind_1,iterate(f,x)(n)))"))
    (contrapose "with(p:prop,not(p));")
    extensionality
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) iterate)
    (case-split-on-conditionals (0))
    (backchain "with(p:prop,forall(u_$0:zz,p));")
    simplify
    )))

(def-theorem iterate-translate
  "forall(n:zz,x:ind_1,f:[ind_1,ind_1],
     f oo (iterate(f,x))=lambda(n:zz,if(n=[-1],?ind_1,iterate(f,x)(n+1))))"
  (theory generic-theory-1)
  (usages transportable-macete)

  ;; 1. Apply direct-inference and then unfold iterate in 
  ;;	iterate(f,x)(n+1).
  ;; 2. Apply commands extensionality, direct-inference, and
  ;;    simplify-insistently.
  ;; 3. Instantiate the theorem undefined-for-negative.
  ;; 4. Ground the remaining two subgoals with simplify and 
  ;;    case-split-on-conditionals.

  (proof (direct-and-antecedent-inference-strategy
	  (unfold-single-defined-constant (1) iterate)
	  extensionality
	  direct-and-antecedent-inference-strategy
	  simplify-insistently
	  (case-split-on-conditionals (0))
	  (instantiate-theorem undefined-for-negative ("x_0" "x" "f"))
	  simplify
	  (contrapose "with(x_0:zz,not(x_0<0));")
	  simplify
	  simplify)))

(def-theorem iterate-totality
  "total_q{iterate,[[ind_1,ind_1],ind_1,[zz,ind_1]]}"
  (theory generic-theory-1)
  (usages d-r-convergence transportable-macete)

  ;; Use insistent-direct-inference followed by unfolding iterate
  ;; grounds formula.

  (proof
   (

    insistent-direct-inference
    (unfold-single-defined-constant (0) iterate)

    )))


; PART IV: Iteration of Functions satisfying Lipschitz%bound

(set (current-theory) (name->theory 'metric-spaces))

; The following def-form builds a theory interpretation which
; translates the sort ind_1 to pp, holding everything else fixed.

(def-translation ind_1->pp
  (source generic-theory-1)
  (target metric-spaces)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 "pp")))

; The recursively defined constant "iterate" is transported to the
; theory metric-spaces.

(def-transported-symbols iterate
  (translation ind_1->pp))

; The theorem "iterate-totality" is also transported to metric-spaces.

(def-theorem nil
  iterate-totality
  ;; "total_q{iterate,[[pp,pp],pp,[zz,pp]]}"
  (theory metric-spaces)
  (translation ind_1->pp)
  (usages d-r-convergence)
  (proof existing-theorem))

; We need to consider the theory of metric spaces as an instance of a
; theory of metric space pairs so we can use constants naturally
; defined in that theory such as "continuous" and "lipschitz%bound."

;;(ensemble-dont-translate-constant metric-spaces "iterate")

(dont-translate-constant ms-ensemble (qr "iterate"))

(def-theory-ensemble-instances
  metric-spaces
  (permutations (0 1))
  (sorts (pp pp pp))
  (constants (dist dist dist))
  (target-theories metric-spaces metric-spaces))

(def-theory-ensemble-overloadings metric-spaces (1 2))

(def-theorem iterated-distance-bound
  "forall(f:[pp,pp],x:pp,p:zz,r:rr, 
     lipschitz%bound(f,r) and  0<=p 
      implies 
     dist(iterate(f,x)(p),iterate(f,x)(p+1))<=r^p*dist(x,f(x)))"
  (theory metric-spaces)

  ;; 1. Unfold lipschitz%bound and then unfold lipschitz%bound%on.
  ;; 2. Use direct-and-antecedent-inference-strategy.
  ;; 3. Use induction with integer-inductor.
  ;; 4. Unfold iterate in iterate(f,x)(2+t) and simplify.
  ;; 5. Instantiate the universal antecedent with iterate(f,x)(t)
  ;;    and iterate(f,x)(1+t).
  ;; 6. Apply simplify-antecedent to the first two subgoals.
  ;; 7. Prove last subgoal by twice using the macete 
  ;;    transitivity-of-<= to interpolate a variable between the 
  ;;    two sides of the inequality.

  (proof
   ((unfold-single-defined-constant (0) lipschitz%bound)
    (unfold-single-defined-constant (0) lipschitz%bound%on)
    direct-and-antecedent-inference-strategy
    (induction integer-inductor ("p"))
    (unfold-single-defined-constant (1) iterate)
    simplify
    (instantiate-universal-antecedent "with(r:rr,f:[pp,pp],
  forall(x_$0,y_$0:pp,
    x_$0 in sort_to_indic{pp} and y_$0 in sort_to_indic{pp}
     implies 
    dist(f(x_$0),f(y_$0))<=r*dist(x_$0,y_$0)));" ("(iterate(f,x)(t))" "(iterate(f,x)(1+t))"))
    (simplify-antecedent "with(t:zz,x:pp,f:[pp,pp],
  not(iterate(f,x)(t) in sort_to_indic{pp}));")
    (simplify-antecedent "with(t:zz,x:pp,f:[pp,pp],
  not(iterate(f,x)(1+t) in sort_to_indic{pp}));")
    (apply-macete-with-minor-premises transitivity-of-<=)
    auto-instantiate-existential
    (force-substitution "r^(1+t)" "r*r^t" (0))
    simplify
    simplify)))
 
;;; !!!!!

(def-theorem iterate-estimate
  "forall(f:[pp,pp],x:pp,p,q:zz,r:rr,
     lipschitz%bound(f,r) and 0<r and r<1 and 1<=p and p<=q and 0<dist(x,f(x)) 
      implies 
     dist(iterate(f,x)(p),iterate(f,x)(q+1))<= dist(x,f(x))*r^p/(1-r))"
  (theory metric-spaces)

  ;; 1. Use direct-and-antecedent-inference-strategy.
  ;; 2. Use macete transitivity-of-<= to interpolate a variable
  ;;    between the two sides of the inequality.  Instantiate the
  ;;    interpolated variable with
  ;;    sum(p,q,lambda(j:zz,dist(iterate(f,x)(j),iterate(f,x)(j+1)))).
  ;; 3. The resulting subgoals, other than the inequality, are proved
  ;;    by applying the commands direct-inference, simplify, 
  ;;    auto-instantiate-existential, and the following macetes:
  ;;     -- generalized-triangle-inequality
  ;;     -- tr%iterate-definedness
  ;;     -- tr%lipschitz-bound-is-total
  ;; 4. Use macete transitivity-of-<= to interpolate a variable
  ;;    between the two sides of the inequality; instantiate the 
  ;;    interpolated variable with sum(p,q,lambda(j:zz,r^j*dist(x,f(x)))).
  ;; 5. On the first subgoal, apply macete mononicity-for-sum; apply
  ;;    macete iterated-distance-bound (after massaging the formula
  ;;    slightly); and then simplify.
  ;; 6. On the second subgoal, use force substitution to reduce the
  ;;    <=-inequality to a <-inequality, apply macete 
  ;;    geometric-series-upper-estimate, and then simplify.

  (proof 
   (

    
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential
     ("sum(p,q,lambda(j:zz,dist(iterate(f,x)(j),iterate(f,x)(j+1))))"))
    (apply-macete-with-minor-premises generalized-triangle-inequality)
    (apply-macete-with-minor-premises tr%iterate-definedness)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%lipschitz-bound-is-total)
    (instantiate-existential ("r"))
    simplify
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("sum(p,q,lambda(j:zz,r^j*dist(x,f(x))))"))
    (apply-macete-with-minor-premises monotonicity-for-sum)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises iterated-distance-bound)
    direct-and-antecedent-inference-strategy
    simplify
    (cut-with-single-formula
     "sum(p,q,lambda(j:zz,r^j*dist(x,f(x)))) <dist(x,f(x))*(r^p/(1-r))")
    simplify
    (apply-macete-with-minor-premises geometric-series-upper-estimate)
    simplify
    (apply-macete-with-minor-premises sum-definedness)
    direct-and-antecedent-inference-strategy
    beta-reduce-repeatedly
    definedness
    (apply-macete-with-minor-premises tr%iterate-definedness)
    (apply-macete-with-minor-premises tr%lipschitz-bound-is-total)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("r"))
    simplify
    (apply-macete-with-minor-premises tr%iterate-definedness)
    direct-and-antecedent-inference-strategy
    simplify
    direct-and-antecedent-inference-strategy
    ))
  )


(def-theorem iterates-are-cauchy
  "forall(f:[pp,pp],x:pp ,r:rr,
     lipschitz%bound(f,r) and r<1 and 0<dist(x,f(x)) 
      implies 
     cauchy(iterate(f,x)))"
  (theory metric-spaces)

  ;; 1. Use direct-and-antecedent-inference-strategy.
  ;; 2. Cut with 0<r; note: lipschitz%bound(f,r) includes 0<r.
  ;; 3. Unfold cauchy, then direct-and-antecedent-inference-strategy.
  ;; 4. Instantiate the theorem powers-corollary with r and 
  ;;	(1-r)*eps/dist(x,f(x)).  (We do this in order to use
  ;;    iterate-estimate.)
  ;; 5. To prove the first ungrounded subgoal, contrapose with
  ;;    not(0<(1-r)*eps/dist(x,f(x))), apply macete
  ;;    fractional-expression-manipulation, and simplify.
  ;; 6. On the second ungrounded subgoal, instantiate p with n; use
  ;;    macete transitivity-of-<= to interpolate a variable between 
  ;;    the two sides of the inequality; instantiate the interpolated 
  ;;    variable with dist(x,f(x))*r^n/(1-r)
  ;; 7. To prove the inequality subgoal, use force-substitution to 
  ;;    rewrite q as (q-1)+1, apply the macete iterate-estimate, and
  ;;    then simplify.
  ;; 8. To prove the remaining subgoals, use simplify plus the macetes:
  ;;     -- fractional-expression-manipulation
  ;;     -- tr%iterate-definedness
  ;;     -- tr%lipschitz-bound-is-total

  (proof

   (

    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "0<r")
    (unfold-single-defined-constant (0) cauchy)
    direct-and-antecedent-inference-strategy
    (instantiate-theorem powers-corollary ("r" "(1-r)*eps/dist(x,f(x))"))
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (instantiate-existential ("n"))
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("dist(x,f(x))*r^n/(1-r)"))
    (force-substitution "q" "(q-1)+1" (0))
    (apply-macete-with-minor-premises iterate-estimate)
    simplify
    simplify
    (incorporate-antecedent "with(n:zz,r:rr,r^n<r*r);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (apply-macete-with-minor-premises tr%iterate-definedness)
    (apply-macete-with-minor-premises tr%lipschitz-bound-is-total)
    simplify
    (instantiate-existential ("r"))
    (incorporate-antecedent "with(r:rr,f:[pp,pp],lipschitz%bound(f,r));")
    (unfold-single-defined-constant (0) lipschitz%bound)
    (unfold-single-defined-constant (0) lipschitz%bound%on)
    direct-and-antecedent-inference-strategy
    )))


; PART IV: The Theorem

(def-theorem fixed-point-trivial-case
  "forall(f:[pp,pp], x:pp, dist(x,f(x))=0 implies forsome(y:pp,f(y)=y))"
  (theory metric-spaces)

  ;; Instantiate y with x and then apply the macetes
  ;; point-separation-for-distance and symmetry-of-distance.

  (proof 

   (
    
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x"))
    (apply-macete-with-minor-premises point-separation-for-distance)
    (apply-macete-with-minor-premises symmetry-of-distance)
    )))


(def-theorem contractive-mapping-fixed-point-theorem
  "forall(f:[pp,pp],r:rr, 
     complete and lipschitz%bound(f,r) and r<1 
      implies 
     forsome(x:pp,f(x)=x))"
  (theory metric-spaces)

  ;; The fixed point is lim(iterate(f,x)). We have to show:
  ;;   o This makes sense.
  ;;   o This is the right guess.

  ;; Note: The command auto-instantiate-existential is often useful in 
  ;; this proof.
  ;;
  ;; 1.  After using direct-and-antecedent-inference-strategy, cut with
  ;;     total_q(f,[pp,pp]). Handle the cut obligation by applying a macete
  ;;     and auto-instantiate-existential.

  ;; 2.  Cut with dist(x,f(x))=0 or 0<dist(x,f(x)).  Handle the cut obligation by
  ;;     simplification.
  ;; 3.  Do an antecedent-inference. One of the cases follows using the macete
  ;;     fixed-point-trivial-case and auto-instantiate-existential.

  ;; 4.  Instantiate x with lim(iterate(f,x)).
  ;;
  ;; Prove fixed point property as follows:
  ;; 5.  Apply the macetes tr%lim-preservation-rev, tr%iterate-translate.
  ;; 6.  Use the command force-substitution to replace
  ;;        lambda(n:zz,if(n=[-1], ?pp, iterate(f,x)(n+1))) with
  ;;        lambda(m:zz, lambda(n:zz,if(n=0, ?pp, iterate(f,x)(n)))(1*m+1)).
  ;; 7.  Apply the macetes limit-translation-invariance and limit-depends-on-tail.
  ;; 8.  Do direct-and-antecedent-inference-strategy.
  ;; 9.  Instantiate the resulting existential with some  m>=1, simplify, 
  ;; 10. Apply the macete tr%iterate-definedness and simplify again.

  ;; Now prove the definedness of lim(iterate(f,x)):
  ;; 11. First of all weaken to get rid of unnecessary assumptions.
  ;; 12. Incorporate "complete" into the assertion, (to be able to apply
  ;;     the unfold command,) do direct-inference, backchain.
  ;; 13. Apply the macete iterates-are-cauchy, Auto-instantiate-existential.
  ;; 14. Replace lim(lambda(n:zz,if(n=0, ?pp, iterate(f,x)(n)))) with lim(iterate(f,x))
  ;; 15. For the remaining nodes either
  ;;    -- simplify or 
  ;;    -- apply the macete tr%lipschitz-bound-is-continuous.

  (proof 

   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "total_q(f,[pp,pp])")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises tr%lipschitz-bound-is-total)
    auto-instantiate-existential
    (cut-with-single-formula "dist(x,f(x))=0 or 0<dist(x,f(x))")
    (move-to-sibling 1)
    simplify
    (antecedent-inference "with(p:prop,p or p);")
    (instantiate-existential ("x"))
    (apply-macete-with-minor-premises point-separation-for-distance)
    (apply-macete-with-minor-premises symmetry-of-distance)

    )))

