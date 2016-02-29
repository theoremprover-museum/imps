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

(herald real-derivatives)

(load-section abstract-calculus)

(def-translation normed-spaces-to-rr

  (source normed-linear-spaces)
  (target h-o-real-arithmetic)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (uu rr))
  (constant-pairs (++ +)
		  (** *)
		  (v0 0)
		  (norm abs))
  (theory-interpretation-check using-simplification))

(def-translation mappings-on-interval-into-ns-to-rr
  (source mappings-from-an-interval-to-a-normed-space)
  (target fixed-interval-theory)
  (core-translation normed-spaces-to-rr)
  (theory-interpretation-check using-simplification))

(def-renamer calculus-renamer
  (pairs 
   (deriv rr%deriv)
   (primitive rr%primitive)
   (integral rr%integral)))

(def-transported-symbols (deriv primitive integral)
  (translation  mappings-on-interval-into-ns-to-rr)
  (renamer calculus-renamer)
  )


;; For instance:


(def-theorem additivity-of-rr-derivative

  "forall(f,g:[ii,rr],x:ii,
    #(rr%deriv(f,x)) and #(rr%deriv(g,x))
      implies 
     rr%deriv(lambda(x:ii,f(x)+g(x)),x)
     =rr%deriv(f,x)+rr%deriv(g,x));"

  (theory fixed-interval-theory)
  (proof
   (


    (apply-macete-with-minor-premises tr%additivity-of-deriv)
    simplify

    )))
