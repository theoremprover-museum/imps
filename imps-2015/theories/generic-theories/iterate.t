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

(herald iterate)

(def-recursive-constant iterate
  "lambda(iter:[zz,ind_1], f:[ind_1,ind_1],x:ind_1,
     lambda(n:zz, if(n=0,x,f(iter(n-1)))))"
  (theory generic-theory-1)
  (definition-name iterate))

(def-theorem iterate-definedness
  "forall(f:[ind_1,ind_1],x:ind_1,z:zz, 
     total_q{f,[ind_1,ind_1]} and 0<=z implies #(iterate(f,x)(z)))"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof 

   (
    (induction integer-inductor ())

    )))

(def-theorem undefined-for-negative
  "forall(n:zz,x:ind_1,f:[ind_1,ind_1],n<0 implies not(#(iterate(f,x)(n))))"
  (theory generic-theory-1)
  (usages transportable-macete)

  (proof

   (

    (instantiate-theorem iterate-minimality_generic-theory-1 ("f" "x"))
    (instantiate-universal-antecedent "with(f:[ind_1,ind_1],x:ind_1,
  forall(h_0:[zz,ind_1],
    h_0=lambda(n:zz,if(n=0, x, f(h_0(n-1))))
     implies 
    forall(u_0:zz,
      #(iterate(f,x)(u_0))
       implies 
      iterate(f,x)(u_0)=h_0(u_0))));" ("lambda(n:zz,if(n<0,?ind_1,iterate(f,x)(n)))"))
    (contrapose "with(p:prop, not(p))")
    extensionality
    direct-inference
    (unfold-single-defined-constant (0) iterate)
    (case-split ("x_0<0"))
    simplify
    simplify
    direct-inference
    (backchain "with(p:prop, t:ind_1,  forall(u:zz, #(t) implies p))")
    simplify


    )))


(def-theorem iterate-translate
  "forall(n:zz,x:ind_1,f:[ind_1,ind_1],
     f oo (iterate(f,x))=lambda(n:zz,if(n=[-1],?ind_1,iterate(f,x)(n+1))))"
  (theory generic-theory-1)
  (usages transportable-macete)

  (proof


   (

    
    direct-inference
    (unfold-single-defined-constant (1) iterate)
    extensionality
    direct-inference
    simplify-insistently
    (instantiate-theorem undefined-for-negative ("x_0" "x" "f"))
    simplify
    simplify

    ))

  )

(def-theorem iterate-totality
  "total_q{iterate,[[ind_1,ind_1],ind_1,[zz,ind_1]]}"
  (theory generic-theory-1)
  (usages d-r-convergence transportable-macete)

  (proof 

   (

    insistent-direct-inference
    (unfold-single-defined-constant (0) iterate)


    )))

