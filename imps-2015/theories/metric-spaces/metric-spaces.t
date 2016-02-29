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


(herald METRIC-SPACES)

(load-section foundation)

(include-files
 (files (imps theories/generic-theories/covers)))


(def-language METRIC-SPACES-LANGUAGE
  (embedded-languages h-o-real-arithmetic)
  (base-types pp)
  (constants 
   (dist (pp pp rr))))
      
(def-theory METRIC-SPACES
  (component-theories h-o-real-arithmetic)
  (language metric-spaces-language)
  (axioms
   (positivity-of-distance
    "forall(x,y:pp, 0<=dist(x,y))" transportable-macete)
   (point-separation-for-distance
    "forall(x,y:pp, x=y iff dist(x,y)=0)" transportable-macete)
   (symmetry-of-distance
    "forall(x,y:pp, dist(x,y) = dist(y,x))" transportable-macete)
   (triangle-inequality-for-distance
    "forall(x,y,z:pp, dist(x,z)<=dist(x,y)+dist(y,z))" transportable-macete)))

(def-theory-ensemble METRIC-SPACES (fixed-theories h-o-real-arithmetic))


;;; Definitions

(def-constant BALL
  "lambda(x:pp,r:rr,indic{y:pp, dist(x,y)<=r})"
  (theory metric-spaces)
  (usages transportable-macete))

(def-constant OPEN%BALL
  "lambda(x:pp,r:rr,indic{y:pp, dist(x,y)<r})"
  (theory metric-spaces)
  (usages transportable-macete))

(def-constant OPEN
  "lambda(o:sets[pp],forall(x:pp, x in o implies
forsome(delta:rr,0<delta and ball(x,delta) subseteq o)))"
 (theory metric-spaces)
 (usages transportable-macete))

(def-constant CONNECTED
  "lambda(x:sets[pp],forall(a,b:sets[pp],open(a) and open(b) and empty_indic_q((a inters b) inters x) and x subseteq a union b implies (x subseteq a or x subseteq b)))"
 (theory metric-spaces)
 (usages transportable-macete))

(def-constant COMPACT
  "lambda(a:sets[pp], forall(f:[zz,sets[pp]],forall(i:zz,#(f(i)) implies open(f(i))) and countable%cover(f,a) implies finite%cover(f,a)))"
  (theory metric-spaces)
  (usages transportable-macete))

(define MS-ENSEMBLE (name->theory-ensemble 'metric-spaces))



 
