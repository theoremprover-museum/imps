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
;% COPYRIGHT NOTICE INSERTED: Fri Oct  7 15:33:41 EDT 1994

(def-constant ff%dist
  "lambda(f,g:ff, fn%dist(f,g))"
  (theory graded-monoid))

(def-theorem ff%dist-is-bounded
  "forall(f,g:ff, ff%dist(f,g)<=1)"
  (theory graded-monoid)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally ff%dist)
    (cut-with-single-formula "forsome(f_1,g_1:total%fns, f=f_1 and g=g_1)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,p);")
     (backchain "with(p:prop,p);")
     (backchain "with(p:prop,p);")
     (weaken (0))
     (apply-macete-with-minor-premises tr%fn%dist-is-bounded))
    (instantiate-existential ("f" "g"))

    )))


(def-theorem stop-is-in-ff
  "#(stop_ff,ff)"
  (theory graded-monoid)
  lemma
  (proof
   (


    (apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory)
    (apply-macete-with-minor-premises stop-is-a-failure)


    )))


(def-theorem positivity-of-ff%dist
  "forall(x,y:ff,0<=ff%dist(x,y))"
  lemma
  (theory graded-monoid)
  (proof
   (


    (unfold-single-defined-constant-globally ff%dist)
    (apply-macete-with-minor-premises graded-monoid-fn%dist-non-negative)

    )))

(def-theorem ()
  "forall(x,y:ff,x=y iff ff%dist(x,y)=0)"
  (theory graded-monoid)
  lemma
  (proof
   (


    (unfold-single-defined-constant-globally ff%dist)
    (apply-macete-with-minor-premises graded-monoid-fn%dist-reflexive)


    )))

(def-theorem ()
  "forall(x,y:ff,ff%dist(x,y)=ff%dist(y,x))"
  (theory graded-monoid)
  lemma
  (proof
   (


    (unfold-single-defined-constant-globally ff%dist)
    (apply-macete-locally graded-monoid-fn%dist-symmetric (0) "fn%dist(x,y)")
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "0<=fn%dist(y,x)")
    (apply-macete-with-minor-premises graded-monoid-fn%dist-non-negative)

    )))

(def-theorem ()
  "forall(x,y,z:ff,ff%dist(x,z)<=ff%dist(x,y)+ff%dist(y,z))"
  (theory graded-monoid)
  lemma
  (proof
   (


    (unfold-single-defined-constant-globally ff%dist)
    (apply-macete-with-minor-premises graded-monoid-fn%dist-triangle-inequality)
    )))




(def-translation pointed-metric-space-to-graded-monoid
  force-under-quick-load
  (source pointed-metric-spaces)
  (target graded-monoid)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (pp ff))
  (constant-pairs (a_0 stop_ff) (dist ff%dist))
  (theory-interpretation-check using-simplification))

(def-renamer pms-to-gm
  (pairs
   (complete ff%complete)
   (cauchy ff%cauchy)
   (lim ff%lim)))

(def-transported-symbols (complete cauchy lim)
  (translation pointed-metric-space-to-graded-monoid)
  (renamer pms-to-gm)
  )

(def-theorem ff-completeness
  "ff%complete"
  (theory graded-monoid)
  (proof
   (

    (cut-with-single-formula "sub%complete")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises completeness-of-ff)
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (incorporate-antecedent "sub%complete;")
     unfold-defined-constants
     unfold-defined-constants
     (unfold-single-defined-constant-globally ff%dist))

    )))

(def-theory parametrized-graded-monoid
  (component-theories graded-monoid generic-theory-1))

(def-theorem ()
  "forsome(h:[ind_1,ff],total_q{h,[ind_1,ff]})"
  (theory parametrized-graded-monoid)
  (proof
   (


    (instantiate-existential ("with(f:ff, lambda(x:ind_1,f))"))
    simplify-insistently

    )))

(def-theorem ()
  "forall(h:[ind_1,ff],
      total_q{h,[ind_1,ff]}
       iff 
      (total_q{h,[ind_1,ff]}
       and 
      #(sup(lambda(a:rr,
              if(forsome(u:ind_1,
                   a=ff%dist(stop_ff,h(u))),
                an%individual,
                ?unit%sort))))))"
  (theory parametrized-graded-monoid)
  lemma
  (proof
   (



    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
     simplify-insistently
     (instantiate-existential ("with(u:ind_1, ff%dist(stop_ff,h(u)))"))
     (block 
      (script-comment "`instantiate-existential' at (0)")
      (instantiate-existential ("u"))
      (cut-with-single-formula "0<=ff%dist(stop_ff,h(u))")
      (apply-macete-with-minor-premises positivity-of-ff%dist)
      (apply-macete-with-minor-premises stop-is-in-ff))
     (cut-with-single-formula "0<=ff%dist(stop_ff,h(u))"))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (1 0)")
     (instantiate-existential ("1"))
     (unfold-single-defined-constant-globally majorizes)
     simplify-insistently
     direct-and-antecedent-inference-strategy
     (backchain "with(r,x_$0:rr,x_$0=r);")
     (apply-macete-with-minor-premises ff%dist-is-bounded))

    )))

(def-translation mappings-into-a-pointed-metric-space-to-parametrized-graded-monoid
  force-under-quick-load
  (source mappings-into-a-pointed-metric-space)
  (target parametrized-graded-monoid)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (bfun (pred "lambda(x:[ind_1, ff], total_q{x,[ind_1 -> ff]})")))
  (core-translation pointed-metric-space-to-graded-monoid)  
  (theory-interpretation-check using-simplification))

;;Next we have to define the distance:

(def-renamer mpms-to-pgm
  (pairs
   (bfun%dist ff%dist_p)))


(def-transported-symbols (bfun%dist)
  (translation mappings-into-a-pointed-metric-space-to-parametrized-graded-monoid)
  (renamer  mpms-to-pgm)
  )

(def-theorem ()
  "forall(x,y,z:bfun, bfun%dist(x,z)<=bfun%dist(x,y)+bfun%dist(y,z))"
  lemma
  (theory parametrized-graded-monoid)
  (translation mappings-into-a-pointed-metric-space-to-parametrized-graded-monoid)
  (proof existing-theorem))

(def-theorem ()
  "forall(x,y:bfun, 0<=bfun%dist(x,y))"
  lemma
  (theory parametrized-graded-monoid)
  (translation mappings-into-a-pointed-metric-space-to-parametrized-graded-monoid)
  (proof existing-theorem))

(def-theorem ()
  "forall(x,y:bfun, bfun%dist(x,y)=bfun%dist(y,x))"
  lemma
  (theory parametrized-graded-monoid)
  (translation mappings-into-a-pointed-metric-space-to-parametrized-graded-monoid)
  (proof existing-theorem))

(def-theorem ()
  "forall(x,y:bfun, x=y iff bfun%dist(x,y)=0)"
  lemma
  (theory parametrized-graded-monoid)
  (translation mappings-into-a-pointed-metric-space-to-parametrized-graded-monoid)
  (proof existing-theorem))

(def-theorem ()
  "forall(f,g:[ind_1,ff],
      #(ff%dist_p(f,g))
       implies 
      total_q{f,[ind_1,ff]} and total_q{g,[ind_1,ff]})"
  lemma
  (theory parametrized-graded-monoid)
  (proof
   (

    (unfold-single-defined-constant-globally ff%dist_p)
    simplify

    )))


(def-theory-ensemble-instances metric-spaces
  force-under-quick-load
  (permutations (0) (0 1))
  (sorts (pp (pred "lambda(x:[ind_1, ff], total_q{x,[ind_1 -> ff]})")
	     (pred "lambda(x:[ind_1, ff], total_q{x,[ind_1 -> ff]})")))
  (constants (dist ff%dist_p ff%dist_p))
  (target-theories parametrized-graded-monoid parametrized-graded-monoid)
  (special-renamings
   (complete ff%complete_p)
   (contraction ff%contraction_p)
   (mu ff%mu_p)))

(def-theorem parametrized-completeness
  "ff%complete_p"
  (theory parametrized-graded-monoid)
  (proof
   (


    (assume-transported-theorem 
     bfun-completeness
     mappings-into-a-pointed-metric-space-to-parametrized-graded-monoid)
    (backchain "with(p:prop,p);")
    (apply-macete-with-minor-premises ff-completeness)

    )))

(def-theorem parametrized-definedness-of-mu-for-contractions-lemma
  definedness-of-mu-for-contractions
  lemma
  (theory parametrized-graded-monoid)
  (translation metric-spaces-to-parametrized-graded-monoid)
  (proof existing-theorem))


(def-theorem parametrized-condition-for-contractions-on-function-spaces-lemma
  condition-for-contractions-on-function-spaces
  lemma
  (theory parametrized-graded-monoid)
  (translation mappings-into-a-pointed-metric-space-to-parametrized-graded-monoid)
  (proof existing-theorem))


(def-atomic-sort ff_p
  "lambda(x:[ind_1, ff], total_q{x,[ind_1 -> ff]})"
  (theory parametrized-graded-monoid))
  

(def-theorem parametrized-definedness-of-mu-for-contractions
  "forall(f:[ff_p->ff_p], 
          ff%contraction_p(f) and total_q{f,[ff_p->ff_p]}
            implies 
          #(ff%mu_p(f)))"
  (theory parametrized-graded-monoid)
  (proof
   (


    (unfold-single-defined-constant-globally ff%contraction_p)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises parametrized-definedness-of-mu-for-contractions-lemma)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises parametrized-completeness)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (2)")
     (unfold-single-defined-constant-globally ff%contraction_p)
     simplify-insistently
     auto-instantiate-existential)
    (backchain "with(f:[ff_p,ff_p],total_q{f,[ff_p,ff_p]});")
    )))