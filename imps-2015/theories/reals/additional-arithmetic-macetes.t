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


(herald additional-arithmetic-macetes)

(load-section foundation)

(def-theorem cut-interval-at-left
  "forall(x,y,z:zz, x<z implies ((x<=y and y<=z) iff (y=x or (x+1<=y and y<=z))))"
  (proof
   (

    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify
    simplify

    ))
  (theory h-o-real-arithmetic))

(def-theorem trivial-interval
  "forall(x,y,z:zz, x=z implies ((x<=y and y<=z) iff y=x))"

  (proof
  

   (

    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify


    ))

  (theory h-o-real-arithmetic))

;;; This macete transforms a formula of the form    a<=x and x<=b,    where
;;; a and b are integers with a<=b and x is a variable, to a disjunction 
;;; of the form    x=a or x=a+1 or x=a+2 or ... or x=b-1 or x=b.

(def-compound-macete
  decompose-interval
  (series
   (repeat cut-interval-at-left)
   trivial-interval
   simplify))

