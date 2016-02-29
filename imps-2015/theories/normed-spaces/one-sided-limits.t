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

(herald one-sided-limits)

(include-files
 (files (imps theories/metric-spaces/inequalities-and-continuity)
	(imps theories/normed-spaces/normed-spaces)))

(def-theory mappings-from-an-interval-to-a-normed-space
  (component-theories fixed-interval-theory normed-linear-spaces))

;; First regard the pair (ii,uu) is an instance of a metric space pair. This
;; will automatically install continuous, continuous%at%point 
;; in mappings-from-an-interval-to-a-normed-space

(def-theory-ensemble-instances
  metric-spaces 
  force-under-quick-load
  (target-theories fixed-interval-theory normed-linear-spaces)
  (permutations (0 1))
  (theory-interpretation-check using-simplification)
  (sorts (pp ii uu))
  (constants (dist "lambda(x,y:ii, abs(x-y))" "lambda(x,y:uu, norm(x-y))"))
  (special-renamings
   (continuous continuous%ii%uu)
   (uniformly%continuous uniformly%continuous%ii%uu)
   (lipschitz%bound uu%lipschitz%bound)
   (lipschitz%bound%on uu%%lipschitz%bound%on)))

(def-theory-ensemble-overloadings metric-spaces (1 2))

(def-translation mapint-to-mapint-normed-space
  (source mappings-from-an-interval)
  (target mappings-from-an-interval-to-a-normed-space)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (pp uu))
  (constant-pairs (dist "lambda(x,y:uu, norm(x-y))"))
  (theory-interpretation-check using-simplification))

(def-constant rlim
  "lambda(f:[ii,uu], x:ii,
          iota(y:uu, 
               forall(eps:rr, 
                       0<eps 
                         implies
                       forsome(z_0:ii, x<z_0 and 
                         forall(z:ii,x<z and z<=z_0 implies norm(f(z)-y) <= eps)))))"
  (theory mappings-from-an-interval-to-a-normed-space))

(def-theorem iota-free-characterization-of-rlim
  "forall(x:ii,f:[ii,uu],v:uu,
     rlim(f,x)=v
      iff 
     forall(eps:rr,
         0<eps
          implies 
         forsome(z_0:ii,
           x<z_0
            and 
           forall(z:ii,x<z and z<=z_0 implies norm(f(z)-v) <= eps))))"

  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof
   (

    (unfold-single-defined-constant (0) rlim)
    direct-and-antecedent-inference-strategy
    (contrapose "with(v,u:uu,u=v);")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    (contrapose "with(p:prop,forall(z_0:ii,p));")
    (antecedent-inference "with(p:prop,p and p);")
    (backchain "with(p:prop,forall(eps:rr,p));")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%metric-separation)
    direct-and-antecedent-inference-strategy
    beta-reduce-repeatedly
    (instantiate-universal-antecedent
     "with(p:prop,forall(eps:rr,0<eps implies forsome(z_0:ii,p)));" ("r"))
    (instantiate-universal-antecedent
     "with(p:prop,forall(eps:rr,0<eps implies forsome(z_0:ii,p)));" ("r"))
    (cut-with-single-formula "forsome(z:ii, x<z and z<=z_$0 and z<=z_0)")
    (antecedent-inference "with(p:prop,forsome(z:ii,p));")
    (instantiate-existential ("f(z)"))
    (backchain "with(r:rr,b:uu,f:[ii,uu],z_0,x:ii,
  forall(z:ii,x<z and z<=z_0 implies norm(f(z)-b)<=r));")
    simplify
    (backchain "with(r:rr,v:uu,f:[ii,uu],z_$0,x:ii,
  forall(z:ii,x<z and z<=z_$0 implies norm(f(z)-v)<=r));")
    simplify
    (cut-with-single-formula "norm(f(z)-v)<=r")
    (cut-with-single-formula "forsome(z:rr, x<z and z<=z_$0 and z<=z_0)")
    (antecedent-inference "with(p:prop,forsome(z:rr,p));")
    (instantiate-existential ("with(z:rr,z)"))
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("z_0" "x"))
    simplify
    (apply-macete-with-minor-premises min-lemma)
    simplify

    )))

(comment;; new-script for previous theorem to apply with modified simplifier


 (unfold-single-defined-constant (0) rlim)
 direct-and-antecedent-inference-strategy
 (contrapose "with(v,u:uu,u=v);")
 (apply-macete-with-minor-premises eliminate-iota-macete)
 (contrapose "with(p:prop,forall(z_0:ii,p));")
 (antecedent-inference "with(p:prop,p and p);")
 (backchain "with(p:prop,forall(eps:rr,p));")
 (apply-macete-with-minor-premises eliminate-iota-macete)
 direct-and-antecedent-inference-strategy
 (apply-macete-with-minor-premises tr%metric-separation)
 direct-and-antecedent-inference-strategy
 beta-reduce-repeatedly
 (instantiate-universal-antecedent "with(b:uu,f:[ii,uu],x:ii,
  forall(eps:rr,
    0<eps
     implies 
    forsome(z_0:ii,
      x<z_0
       and 
      forall(z:ii,
        x<z and z<=z_0 implies norm(f(z)-b)<=eps))));"
				   ("r"))
 (instantiate-universal-antecedent "with(p:prop,forall(eps:rr,0<eps implies forsome(z_0:ii,p)));"
				   ("r"))
 (cut-with-single-formula "forsome(z:ii, x<z and z<=z_$0 and z<=z_0)")
 (antecedent-inference "with(p:prop,forsome(z:ii,p));")
 (instantiate-existential ("f(z)"))
 (backchain "with(r:rr,b:uu,f:[ii,uu],z_0,x:ii,
  forall(z:ii,x<z and z<=z_0 implies norm(f(z)-b)<=r));")
 simplify
 (cut-with-single-formula "norm(f(z)-v)<=r")
 (cut-with-single-formula "forsome(z:rr, x<z and z<=z_$0 and z<=z_0)")
 (antecedent-inference "with(p:prop,forsome(z:rr,p));")
 (instantiate-existential ("with(z:rr,z)"))
 (apply-macete-with-minor-premises interval-characterization)
 (instantiate-existential ("z_0" "x"))
 simplify
 (apply-macete-with-minor-premises min-lemma)

 )

(def-script epsilon/n-argument 1	;eps is a string.
   (
    (while
     (matches? "with(p:prop, p)" "with(p:prop, forall(eps:rr, 0<eps implies p))")
     (block
       (instantiate-universal-antecedent
	"with(p:prop, forall(eps:rr, 0<eps implies p))" ($1))
       (if (matches? "with(p:prop, p)" "with(r:rr, not(0<r))")
	   (simplify-antecedent "with(r:rr, not(0<r))")))

    )))


(def-theorem rlim-additivity
  "forall(f,g:[ii,uu], z:ii, 
                 #(rlim(f,z)) and #(rlim(g,z))
                     implies
                 rlim(lambda(x:ii,f(x)+g(x)),z)=rlim(f,z)+rlim(g,z))"

  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(v,w:uu,rlim(f,z)=v and rlim(g,z)=w)")
    (antecedent-inference "with(p:prop,forsome(v,w:uu,p));")
    (backchain "with(p:prop,p and p);")
    (backchain "with(p:prop,p and p);")
    (incorporate-antecedent "with(p:prop,p and p);")
    (apply-macete-with-minor-premises iota-free-characterization-of-rlim)
    direct-and-antecedent-inference-strategy
    (epsilon/n-argument "eps_$0/2")
    (move-to-ancestor 20)
    (move-to-descendent (1))
    (instantiate-existential ("rlim(f,z)" "rlim(g,z)"))
    (cut-with-single-formula "forsome(theta:ii, z<theta and theta<=z_$0 and theta<=z_$3)")
    (instantiate-existential ("theta"))
    beta-reduce-repeatedly
    (instantiate-universal-antecedent "with(eps_$0:rr,v:uu,f:[ii,uu],z_$0,z:ii,
  forall(z_$2:ii,
    z<z_$2 and z_$2<=z_$0 implies 
    norm(f(z_$2)-v)<=eps_$0/2));"
				      ("z_$1"))
    (simplify-antecedent "with(p:prop,not(p));")
    (instantiate-universal-antecedent "with(p:prop,forall(z_$2:ii,p));" ("z_$1"))
    (simplify-antecedent "with(p:prop,not(p));")
    (cut-with-single-formula "norm((f(z_$1)+g(z_$1))-(v+w))<=norm(f(z_$1)-v)+norm(g(z_$1)-w)")
    simplify
    (force-substitution "(f(z_$1)+g(z_$1))-(v+w)" "(f(z_$1)-v)+(g(z_$1)-w)" (0))
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises norm-triangle-inequality)
    (cut-with-single-formula "forsome(theta:rr,z<theta and theta<=z_$0 and theta<=z_$3)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises min-lemma)
    simplify
    (antecedent-inference "with(p:prop,forsome(theta:rr,p));")
    (instantiate-existential ("with(theta:rr, theta)"))
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("z_$0" "z"))
    simplify

    )))


(def-theorem rlim-homogeneity
  "forall(f:[ii,uu],a:rr,z:ii,
     #(rlim(f,z))
      implies  
     rlim(lambda(x:ii,a*f(x)),z)=a*rlim(f,z))"

  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (


    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(v:uu,rlim(f,z)=v)")
    (antecedent-inference "with(p:prop,forsome(v:uu,p));")
    (backchain "with(v,u:uu,u=v);")
    (incorporate-antecedent "with(v,u:uu,u=v);")
    (apply-macete-with-minor-premises iota-free-characterization-of-rlim)
    direct-and-antecedent-inference-strategy
    (case-split ("a=0"))
    simplify
    (auto-instantiate-universal-antecedent "with(v:uu,f:[ii,uu],z:ii,
  forall(eps_$0:rr,
    0<eps_$0
     implies 
    forsome(z_$1:ii,
      z<z_$1
       and 
      forall(z_$0:ii,
        z<z_$0 and z_$0<=z_$1
         implies 
        norm(f(z_$0)-v)<=eps_$0))));")
    auto-instantiate-existential
    (cut-with-single-formula "0<abs(a)")
    (epsilon/n-argument "eps_$0/abs(a)")
    (move-to-ancestor 1)
    (apply-macete-with-minor-premises positivity-of-inverse)
    auto-instantiate-existential
    beta-reduce-repeatedly
    (force-substitution "a*f(z_$0)-a*v" "a*(f(z_$0)-v)" (0))
    (apply-macete-with-minor-premises norm-scalar-multiplication)
    (instantiate-universal-antecedent "with(p:prop,forall(z_$2:ii,p));" ("z_$0"))
    (incorporate-antecedent "with(r:rr,r<=r);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    simplify
    (case-split ("0<a"))
    (apply-macete-with-minor-premises absolute-value-non-negative)
    (apply-macete-with-minor-premises absolute-value-non-positive)
    simplify
    (instantiate-existential ("rlim(f,z)"))
    )))
