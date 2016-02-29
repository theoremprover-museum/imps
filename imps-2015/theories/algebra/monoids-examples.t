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


(herald monoids-examples)

(include-files
  (files (imps theories/algebra/monoids)))

(def-theorem associative-law-for-multiplication-for-monoids
  associative-law-for-multiplication-for-monoids
  (usages transportable-macete)
  (theory monoid-theory)
  (proof existing-theorem))

(def-theorem reverse-associative-law-for-multiplication-for-monoids
  "forall(z,y,x:uu, (x**y)**z = x**(y**z))"
  (theory monoid-theory)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids)
    simplify
    )))

(def-theorem left-cancellation-law-for-monoids
  "forall(x,y,z:uu, y = z implies x**y = x**z)"
  (theory monoid-theory)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    )
   ))

(def-theorem right-cancellation-law-for-monoids
  "forall(x,y,z:uu, x = y implies x**z = y**z)"
  (usages transportable-macete)
  (theory monoid-theory)
  (proof
   (
    direct-and-antecedent-inference-strategy
    )
   ))

(def-compound-macete monoid-cancellation-laws
  (series
   (repeat 
    reverse-associative-law-for-multiplication-for-monoids
    tr%reverse-associative-law-for-multiplication-for-monoids)
   (repeat 
    left-cancellation-law-for-monoids
    tr%left-cancellation-law-for-monoids)
   (repeat 
    associative-law-for-multiplication-for-monoids
    tr%associative-law-for-multiplication-for-monoids)
   (repeat 
    right-cancellation-law-for-monoids
    tr%right-cancellation-law-for-monoids)))
			  
(def-theorem monoid%prod-distributes-over-**
  "forall(m,n:zz,f,g:[zz,uu],
     m<=n and forall(k:zz, m<=k and k<=n implies #(f(k)) and #(g(k)))
      implies
     monoid%prod(m,n,lambda(i:zz,f(i)**g(i))) = 
     monoid%prod(m,n,f) ** monoid%prod(m,n,g))"
  (theory commutative-monoid-theory)
  (usages transportable-macete)
  (proof
   (
    (induction integer-inductor ("n"))
    (backchain "with(p:prop,p implies p)")
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    (apply-macete-with-minor-premises monoid-cancellation-laws)
    (apply-macete-locally commutative-law-for-monoids 
			  (0)		  
			  "monoid%prod(m,t,g)**f(1+t)")
    simplify
    simplify
    simplify
    )))
