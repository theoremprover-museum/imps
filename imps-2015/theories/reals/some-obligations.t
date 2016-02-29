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


(herald SOME-OBLIGATIONS)

;;; axiom obligation for positivity-of-distance under metric-spaces-to-rr

(def-theorem positivity-of-rr-distance
  "forall(x,y:rr,0<=lambda(x,y:rr,abs(x-y))(x,y))"
 (theory h-o-real-arithmetic)
 (proof
  (simplify)))

;;; axiom obligation for point-separation-for-distance under metric-spaces-to-rr

(def-theorem point-separation-for-rr-distance
  "forall(x,y:rr,x=y iff lambda(x,y:rr,abs(x-y))(x,y)=0)"
 (theory h-o-real-arithmetic)
 (proof
  (
   
   beta-reduce-repeatedly
   (apply-macete-with-minor-premises absolute-value-zero)
   simplify

   )))

;;; axiom obligation for symmetry-of-distance under metric-spaces-to-rr

(def-theorem symmetry-of-rr-distance
  "forall(x,y:rr, lambda(x,y:rr,abs(x-y))(x,y)=
             lambda(x,y:rr,abs(x-y))(y,x))"
  (proof 


   (

    beta-reduce-repeatedly
    (force-substitution "y-x" "[-1]*(x-y)" (0))
    (apply-macete-with-minor-premises absolute-value-product)
    (unfold-single-defined-constant (1) abs)
    simplify
    simplify

    ))
  (theory h-o-real-arithmetic))

;;; axiom obligation for triangle-inequality for distance under metric-spaces-to-rr

(def-theorem triangle-inequality-for-rr-distance
  "forall(x,y,z:rr, lambda(x,y:rr,abs(x-y))(x,z)<=
             lambda(x,y:rr,abs(x-y))(x,y)+lambda(x,y:rr,abs(x-y))(y,z))"
  (proof 


   (

    beta-reduce-repeatedly
    (force-substitution "(x-z)" "(x-y)+(y-z)" (0))
    (apply-macete-with-minor-premises triangle-inequality)
    simplify

    ))

  (theory h-o-real-arithmetic))

(def-theorem sub-is-diff 	
  "sub=lambda(x,y:rr,-y+x)"
 (theory h-o-real-arithmetic)
 (proof
  (
   (prove-by-logic-and-simplification 3)

   )))


