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

(herald mu-operator)

(load-section banach-fixed-point-theorem)

(def-constant mu
  "lambda(f:[pp->pp], iota(x:pp, f(x)=x))"
  (theory metric-spaces))

(def-constant contraction
  "lambda(f: [pp -> pp], 
       forsome(r:rr, 0<r and 
                     r<1 and 
                     forall(x,y:pp, x in dom{f} and y in dom{f}
                       implies
                     dist(f(x),f(y))<=r*dist(x,y))))"
  (theory metric-spaces))
  
(def-theorem iota-free-characterization-of-mu
  "forall(f:[pp->pp], r:rr, x:pp, 
      contraction(f)  implies (mu(f)=x iff f(x)=x))"
  (theory metric-spaces)
  (proof
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
      (contrapose "with(x,p:pp,p=x);")
      (apply-macete-with-minor-premises eliminate-iota-macete)
      (contrapose "with(p:prop,not(p));"))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
      (apply-macete-with-minor-premises eliminate-iota-macete)
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(x,y:pp,p));"
					("b" "x"))
      (simplify-antecedent "with(p:prop,not(p));")
      (simplify-antecedent "with(p:prop,not(p));")
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	(contrapose "with(r:rr,r<=r);")
	(backchain "with(b:pp,f:[pp,pp],f(b)=b);")
	(backchain "with(x:pp,f:[pp,pp],f(x)=x);")
	(contrapose "with(p:prop,not(p));")
	(apply-macete-with-minor-premises point-separation-for-distance)
	(simplify-antecedent "with(r:rr,r<=r);"))))))

(def-theorem definedness-of-mu-for-contractions
  "forall(f:[pp->pp], 
      complete and contraction(f) and total_q{f,[pp->pp]} implies #(mu(f)))"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof
   (

    (unfold-single-defined-constant (0) contraction)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(x:pp, mu(f)=x)")
    (antecedent-inference "with(p:prop,forsome(x:pp,p));")
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises iota-free-characterization-of-mu)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
	(apply-macete-with-minor-premises contractive-mapping-fixed-point-theorem)
	(instantiate-existential ("r"))
	(unfold-single-defined-constant (0) lipschitz%bound)
	(unfold-single-defined-constant (0) lipschitz%bound%on)
	direct-and-antecedent-inference-strategy
	simplify)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (1)")
	(unfold-single-defined-constant-globally contraction)
	auto-instantiate-existential))

    )))

(comment
 (def-theory complete-metric-spaces
   (component-theories metric-spaces)
   (axioms (metric-completeness "complete")))


 (def-theorem contractive-implies-mu-definedness
   "forall(f:[pp->pp], contraction(f) and total_q{f,[pp->pp]} 
	    implies 
	    #(mu(f)))"
   (theory complete-metric-spaces)
   (proof
    (


     (apply-macete-with-minor-premises definedness-of-mu-for-contractions)
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises metric-completeness)
     ))))


(include-files
 (files (imps theories/metric-spaces/mappings-into-pointed-metric-spaces)))
 
(def-theory-ensemble-instances
  metric-spaces
  force-under-quick-load
  (permutations (0))
  (sorts (pp bfun))
  (constants (dist bfun%dist))
  (target-theories mappings-into-a-pointed-metric-space)
  (special-renamings
   (ball bfun%ball)
   (complete bfun%complete)
   (lipschitz%bound%on bfun%lipschitz%bound%on)
   (lipschitz%bound bfun%lipschitz%bound)))

(def-theory-ensemble-overloadings metric-spaces 
  (1 2))

(def-theorem definedness-of-mu-for-contractions-on-functions
  "forall(f:[bfun->bfun], complete and 
                         contraction(f) and 
                         total_q{f,[bfun->bfun]}
                            implies 
                         #(mu(f)))"
  (theory mappings-into-a-pointed-metric-space)
  (proof
   (

    (apply-macete-with-minor-premises tr%definedness-of-mu-for-contractions)
    (apply-macete-with-minor-premises bfun-completeness)
    )))


(def-theorem condition-for-contractions-on-function-spaces
  "forall(f:[bfun->bfun], 
    forsome(k:rr,0<k and k<1 and
         forall(phi,psi:bfun, x:ind_1, 
              forsome(y:ind_1, 
                 dist(f(phi)(x),f(psi)(x))<=k*dist(phi(y),psi(y)))))
      implies
    contraction(f))"
  (theory mappings-into-a-pointed-metric-space)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally contraction_0)
    (instantiate-existential ("k"))
    (unfold-single-defined-constant-globally bfun%dist)
    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (instantiate-universal-antecedent
     "with(p:prop,forall(phi,psi:bfun,x:ind_1,p));"
     ("y" "y" "with(x:ind_1,x)"))
    (move-to-sibling 2)
    (instantiate-universal-antecedent 
     "with(p:prop,forall(phi,psi:bfun,x:ind_1,p));"
     ("x" "x" "with(x:ind_1,x)"))
    (block 
     (script-comment "`beta-reduce-with-minor-premises' at (0)")
     (apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
      (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (0)")
       beta-reduce-with-minor-premises
       direct-and-antecedent-inference-strategy
       (cut-with-single-formula 
	"k^(-1)*dist(f(x)(n_$0),f(y)(n_$0)) <=sup(ran{lambda(x_$0:ind_1,dist(x(x_$0),y(x_$0)))})")
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(incorporate-antecedent "with(r:rr,r<=r);")
	(apply-macete-with-minor-premises fractional-expression-manipulation)
	simplify)
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
	(instantiate-universal-antecedent
	 "with(p:prop,forall(phi,psi:bfun,x:ind_1,p));"
					  ("x" "y" "n_$0"))
	direct-and-antecedent-inference-strategy
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	 (instantiate-existential ("dist(x(y_$0),y(y_$0))"))
	 (block 
	  (script-comment "`instantiate-existential' at (0 0)")
	  simplify-insistently
	  (instantiate-existential ("y_$0")))
	 (block 
	  (script-comment "`instantiate-existential' at (0 1)")
	  (incorporate-antecedent "with(r:rr,r<=r);")
	  (apply-macete-with-minor-premises fractional-expression-manipulation)
	  simplify))
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0)")
	 (cut-with-single-formula "#(bfun%dist(x,y))")
	 (weaken (7 6 5 4 3 2 1))
	 (incorporate-antecedent "with(p:prop,p);")
	 (unfold-single-defined-constant-globally bfun%dist))))
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (1)")
       (cut-with-single-formula "#(bfun%dist(x,y))")
       (weaken (3 2 1 4))))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
      (cut-with-single-formula "#(bfun%dist(f(x),f(y)))")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (weaken (5 4 3 1))
       (incorporate-antecedent "with(r:rr,#(r));")
       (unfold-single-defined-constant-globally bfun%dist)
       beta-reduce-with-minor-premises
       (block 
	(script-comment "`beta-reduce-with-minor-premises' at (1)")
	(simplify-antecedent "with(p:prop,p);"))
       (simplify-antecedent "with(p:prop,p);"))
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (cut-with-single-formula "with(x,y:bfun,n:ind_1,dist(f(x)(n),f(y)(n))<=bfun%dist(f(x),f(y)))")
       (apply-macete-with-minor-premises bounded-bfun%dist))))


    )))