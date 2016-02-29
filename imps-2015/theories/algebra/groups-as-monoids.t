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


(herald groups-as-monoids)

(include-files
  (files (imps theories/algebra/monoids)))

(load-section basic-group-theory)


(def-translation monoids-to-groups
  (source monoid-theory)
  (target groups)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (uu gg))
  (constant-pairs
   (e e)
   (** mul)))

(def-constant MINUS
  "lambda(x,y:gg,inv(y) mul x)"
  (theory groups)
  (usages rewrite))

(def-renamer monoid-to-groups-renamer
  (pairs (monoid%prod group%prod)))

(def-transported-symbols (monoid%prod)
  (translation monoids-to-groups)
  (renamer monoid-to-groups-renamer)
  )

(def-translation groups-to-additive-rr
  (source groups)
  (target h-o-real-arithmetic)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (gg rr))
  (constant-pairs
   (e 0)
   (mul  +)
   (inv -)
   (minus sub)
   (group%prod sum))
  (theory-interpretation-check using-simplification))

(def-constant DELTA
  "lambda(f:[zz,gg],lambda(n:zz,minus(f(n+1),f(n))))"
  (theory groups)
  (usages rewrite))

(def-theorem telescoping-prod-formula
  "forall(f:[zz,gg],m,n:zz,m<=n and
                forall(j:zz,(m<=j and j<=n+1) implies #(f(j)))
                   implies group%prod(m,n,delta(f))=minus(f(n+1),f(m)))"
  (theory  groups)
  (usages transportable-macete)
  (proof


   (

    (induction integer-inductor ())
    (prove-by-logic-and-simplification 3)
    (backchain "with(f:[zz,gg],t,m:zz,
  forall(j:zz,m<=j and j<=1+t implies #(f(j)))
   implies 
  group%prod(m,t,lambda(n:zz,inv(f(n)) mul f(1+n)))
  =inv(f(m)) mul f(1+t));")
    direct-and-antecedent-inference-strategy
    simplify
    simplify


    )))



(def-renamer groups-to-additive-rr-renamer
  (pairs (delta rr%delta)))

(def-transported-symbols (delta)
  (translation groups-to-additive-rr)
  (renamer groups-to-additive-rr-renamer)
  )

(def-overloading delta
  (groups delta) (h-o-real-arithmetic rr%delta))


