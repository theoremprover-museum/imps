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


(herald knaster-fixed-point-theorem)

(include-files
 (files (imps theories/partial-orders/partial-order)))

(def-constant monotone
  "lambda(f:[uu,uu], forall(x,y:uu, x prec y implies f(x) prec f(y)))"
  (theory partial-order))

(def-theorem knaster-fixed-point-theorem
  "forall(f:[uu,uu], 
           forsome(bot,top:uu, forall(x:uu, bot prec x and x prec top))
            and
           monotone(f)
            implies
           forsome(z:uu, f(z)=z))"
  (theory complete-partial-order)
  (usages transportable-macete)
  (proof
   (

    (unfold-single-defined-constant (0) monotone)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "total_q{f,[uu,uu]} and #(prec%sup(indic{x:uu,  x prec f(x)}))")
    (move-to-sibling 1)
    (block (script-comment "node added by `cut-with-single-formula' at (1)")
	   direct-and-antecedent-inference-strategy
	   (block (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0)")
		  insistent-direct-inference
		  (instantiate-universal-antecedent "with(p:prop,forall(x,y:uu,p));"
						    ("x_0" "x_0"))
		  (contrapose "with(p:prop,not(p));")
		  (apply-macete-with-minor-premises prec-reflexivity))
	   (block (script-comment "node added by `direct-and-antecedent-inference-strategy' at (1)")
		  (apply-macete-with-minor-premises prec%sup-defined)
		  direct-and-antecedent-inference-strategy
		  (block (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0)")
			 (instantiate-existential ("bot"))
			 (apply-macete-with-minor-premises indicator-facts-macete)
			 beta-reduce-repeatedly
			 (backchain "with(p:prop,forall(x:uu,p and p));"))
		  (block (script-comment "node added by `direct-and-antecedent-inference-strategy' at (1 0)")
			 (instantiate-existential ("top"))
			 (unfold-single-defined-constant (0) prec%majorizes)
			 (apply-macete-with-minor-premises indicator-facts-macete)
			 beta-reduce-repeatedly
			 direct-and-antecedent-inference-strategy)))
    (block (script-comment "node added by `cut-with-single-formula' at (0)")
	   (instantiate-existential ("prec%sup(indic{x:uu, x prec f(x)})"))
	   (script-comment "we show x_0 prec f(x_0) and f(x_0) prec x_0 separately.")
	   (apply-macete-with-minor-premises prec-anti-symmetry)
	   (cut-with-single-formula "prec%sup(indic{x:uu,  x prec f(x)})
   prec f(prec%sup(indic{x:uu,  x prec f(x)}))")
	   direct-inference
	   (move-to-ancestor 2)
	   (move-to-descendent (1))
	   (block (script-comment "node added by `cut-with-single-formula' at (1)")
		  (apply-macete-with-minor-premises lub-property-of-prec%sup)
		  direct-inference
		  (unfold-single-defined-constant (0) prec%majorizes)
		  (apply-macete-with-minor-premises indicator-facts-macete)
		  beta-reduce-repeatedly
		  direct-and-antecedent-inference-strategy
		  (apply-macete-with-minor-premises prec-transitivity)
		  auto-instantiate-existential
		  (backchain "with(p:prop,forall(x,y:uu,p));")
		  (apply-macete-with-minor-premises minorizes-property-of-prec%sup)
		  direct-inference
		  (instantiate-existential ("x_$0"))
		  (block (script-comment "node added by `instantiate-existential' at (0 0)")
			 (apply-macete-with-minor-premises indicator-facts-macete)
			 beta-reduce-repeatedly)
		  (apply-macete-with-minor-premises prec-reflexivity))
	   (block (script-comment "node added by `direct-inference' at (0)")
		  (cut-with-single-formula "f(prec%sup(indic{x:uu,  x prec f(x)})) in indic{x:uu,  x prec f(x)}")
		  (cut-with-single-formula "prec%sup(indic{x:uu,  x prec f(x)}) prec f(prec%sup(indic{x:uu,  x prec f(x)}))")
		  (move-to-ancestor 2)
		  (move-to-descendent (1))
		  (block (script-comment "node added by `cut-with-single-formula' at (1)")
			 (apply-macete-with-minor-premises indicator-facts-macete)
			 beta-reduce-repeatedly
			 (backchain "with(p:prop,forall(x,y:uu,p));"))
		  (block (script-comment "node added by `cut-with-single-formula' at (0 (1 . 0))")
			 (apply-macete-with-minor-premises minorizes-property-of-prec%sup)
			 direct-and-antecedent-inference-strategy
			 auto-instantiate-existential
			 (apply-macete-with-minor-premises prec-reflexivity))))

    )))


;;Next we want to relativize the knaster fp theorem to intervals.

(include-files
 (files (imps theories/partial-orders/interval-in-cpos)))

(def-renamer cpo-to-interval
  (pairs
   (monotone ii%monotone)))

(def-transported-symbols monotone
  (translation relativize-to-interval)
  (renamer  cpo-to-interval)
  )

(def-theorem relativized-knaster-fixed-point-theorem
  "forall(f:[uu,uu], 
	    ii%monotone(f)
            implies
	    forsome(z:ii, f(z)=z))"
  (home-theory interval-in-cpo)
  (theory complete-partial-order)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (instantiate-transported-theorem knaster-fixed-point-theorem
				     relativize-to-interval
				     ("lambda(z:ii,f(z))"))
    (contrapose "with(p:prop,forall(bot,top:ii,p));")
    (label-node l_0)
    (instantiate-existential ("bot" "top"))
    (jump-to-node l_0)
    (for-nodes 
     (unsupported-descendents)
     (if (matches? "with(a:uu,#(a,ii))")
	 (block
	  (apply-macete-with-minor-premises ii-defining-axiom_interval-in-cpo)
	  (apply-macete-with-minor-premises non-triviality)
	  (apply-macete-with-minor-premises prec-reflexivity))
       (block
	(cut-with-single-formula "#(x,ii)")
	(incorporate-antecedent "with(x:ii,#(x,ii));")
	(apply-macete-with-minor-premises ii-defining-axiom_interval-in-cpo)
	direct-and-antecedent-inference-strategy)))

    (contrapose "with(p:prop,not(p));")
    (incorporate-antecedent "with(f:[uu,uu],ii%monotone(f));")
    (weaken (0))
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(f,[ii,ii])")
    (beta-reduce-antecedent "with(p:prop,f:[uu,uu], lambda(f:[ii,ii],p) (f));")
    beta-reduce-with-minor-premises
    beta-reduce-repeatedly
    (cut-with-single-formula "forsome(g:[ii,ii],f=g)")
    (move-to-sibling 1)
    (weaken (0))
    (instantiate-existential ("f"))
    (antecedent-inference "with(p:prop,forsome(g:[ii,ii],p));")
    (backchain "with(g:[ii,ii],f:[uu,uu],f=g);")
    (instantiate-existential ("z"))
    (beta-reduce-antecedent "with(z:ii,f:[uu,uu],lambda(z:ii,f(z))(z)=z);")
    (incorporate-antecedent "with(p:prop,p);")
    (unfold-single-defined-constant-globally ii%monotone)
    direct-and-antecedent-inference-strategy)))

;;;This is the theorem that is actually installed in complete-partial-order:

(comment "forall(top,bot:uu,
    bot prec top
     implies 
    forall(f:[uu,uu],
      forall(x_0:uu,
        if_form(bot prec x_0 and x_0 prec top,
          #(f(x_0))
           implies 
          bot prec f(x_0) and f(x_0) prec top,
          not(#(f(x_0)))))
       and 
      forall(x,y:uu,
        (bot prec x and x prec top)
         and 
        (bot prec y and y prec top)
         implies 
        (x prec y implies f(x) prec f(y)))
       implies 
      forsome(z:uu,(bot prec z and z prec top) and f(z)=z)))"
)

(def-theorem knaster-fixed-point-theorem-corollary
  "forall(top,bot:uu,f:[uu,uu],
     bot prec top
      and 
     bot prec f(bot)
      and 
     f(top) prec top
      and 
     forall(x,y:uu,
       bot prec x
        and 
       x prec top
        and 
       bot prec y
        and 
       y prec top
        and 
       x prec y
        implies 
       f(x) prec f(y))
      implies 
     forsome(z:uu,(bot prec z and z prec top) and f(z)=z))"
  (theory complete-partial-order)
  (usages transportable-macete)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forall(x:uu, bot prec x and x prec top implies bot prec f(x) and f(x) prec top)")
    (let-script
     prove-cut 1
     (
      (apply-macete-with-minor-premises prec-transitivity)
      direct-inference
      (instantiate-existential ((% "f(~A)" $1)))
      (backchain "with(p:prop,forall(x,y:uu,p));")
      simplify
      (apply-macete-with-minor-premises prec-reflexivity)
      (instantiate-universal-antecedent "with(p:prop,forall(x,y:uu,p));" ("x" "x")))
     )
    (move-to-sibling 1)
    direct-and-antecedent-inference-strategy
    ($prove-cut "bot")
    ($prove-cut "top")
    (cut-with-single-formula
     "forsome(z:uu,(bot prec z and z prec top) and
       lambda(z:uu,if(bot prec z and z prec top,f(z),?uu))(z)=z)")
    (instantiate-existential ("z"))
    (contrapose "with(z,u:uu,p:prop,(p and p) and u=z);")
    simplify
    (label-node l_0)
    (apply-macete-with-minor-premises relativized-knaster-fixed-point-theorem)
    direct-and-antecedent-inference-strategy
    (jump-to-node l_0)
    (for-nodes
     (unsupported-descendents)
     simplify)
    
    
    )))
