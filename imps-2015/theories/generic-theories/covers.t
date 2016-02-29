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


(herald covers)

(load-section foundation)


(def-quasi-constructor COUNTABLE%COVER
 "lambda(v:[zz,sets[ind_1]],a:sets[ind_1],forall(x:ind_1,x in a implies forsome(n:zz,x in v(n))))"
 (fixed-theories h-o-real-arithmetic)
 (language generic-theory-2))

(def-quasi-constructor FINITE%COVER
 "lambda(v:[zz,sets[ind_1]],a:sets[ind_1],forsome(m:zz,forall(x:ind_1,x in a implies forsome(n:zz,-m<=n and n<=m and x in v(n)))))"
 (fixed-theories  h-o-real-arithmetic)
 (language generic-theory-2))

(def-theorem inverse-image-of-covers
  "forall(v:[zz,sets[ind_2]],a:sets[ind_1],f:[ind_1,ind_2],total_q(f,[ind_1,ind_2]) 
 implies
countable%cover(v,image(f,a)) 
 iff
countable%cover(lambda(k:zz,if(#(v(k)), inv_image(f,v(k)), ?sets[ind_1])),a))"
  (usages transportable-macete)
  (theory generic-theory-2)
  (proof 

   (


    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 0)")
     insistent-direct-inference
     direct-and-antecedent-inference-strategy
     beta-reduce-repeatedly
     (instantiate-universal-antecedent
      "with(v:[zz,sets[ind_2]],f:sets[ind_2],countable%cover{v,f});"
      ("f(x_$0)"))
     (block 
      (script-comment "node added by `instantiate-universal-antecedent' at (0 0 0)")
      (contrapose "with(p:prop,not(p));")
      simplify-insistently
      (instantiate-existential ("x_$0")))
     (block 
      (script-comment "node added by `instantiate-universal-antecedent' at (0 0 1 0)")
      (instantiate-existential ("n_$1"))
      simplify))
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 1)")
     insistent-direct-inference
     direct-and-antecedent-inference-strategy
     (contrapose "with(x_$0:ind_2,f:sets[ind_2],x_$0 in f);")
     simplify-insistently
     direct-and-antecedent-inference-strategy
     (contrapose "with(p:prop,forall(n_$0:zz,p));")
     (instantiate-universal-antecedent
      "with(f:[zz,sets[ind_1]],a:sets[ind_1],countable%cover{f,a});"
      ("x"))
     (contrapose "with(x:ind_1,n_$0:zz,f:[zz,sets[ind_1]],x in f(n_$0));")
     beta-reduce-repeatedly
     (contrapose "with(p:prop,forall(n_$0:zz,p));")
     (instantiate-existential ("n_$0"))
     (contrapose "with(x:ind_1,f:sets[ind_1],p:prop,x in if(p, f, f));")
     (raise-conditional (0))
     (contrapose "with(p:prop,not(p));")
     (antecedent-inference "with(p:prop,if_form(p, p, p));")
     (contrapose "with(x:ind_1,
  x
   in inv_image{with(f:[ind_1,ind_2],f),
                with(f:sets[ind_2],f)});")
     simplify)

    )

   ))

(def-theorem inverse-image-of-finite-covers
  "forall(v:[zz,sets[ind_2]],a:sets[ind_1],f:[ind_1,ind_2],total_q(f,[ind_1,ind_2]) 
 implies
finite%cover(v,image(f,a)) 
 iff
finite%cover(lambda(k:zz,if(#(v(k)), inv_image(f,v(k)), ?sets [ind_1])),a))"
  (usages transportable-macete)
  (theory generic-theory-2)
  (proof

   (


    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 0
0)")
     (instantiate-existential ("m_$0"))
     (instantiate-universal-antecedent "with(p:prop,forall(x_$0:ind_2,p));"
				       ("f(x_$0)"))
     (block 
      (script-comment "node added by `instantiate-universal-antecedent' at (0 0 0)")
      (contrapose "with(p:prop,not(p));")
      simplify-insistently
      (instantiate-existential ("x_$0")))
     (block 
      (script-comment "node added by `instantiate-universal-antecedent' at (0 0 1 0 0)")
      (instantiate-existential ("n_$1"))
      beta-reduce-repeatedly
      simplify-insistently))
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 1
0)")
     (instantiate-existential ("m_$0"))
     (contrapose "with(x_$0:ind_2,f:sets[ind_2],x_$0 in f);")
     simplify-insistently
     direct-and-antecedent-inference-strategy
     (instantiate-universal-antecedent "with(p:prop,forall(x_$0:ind_1,p implies p));"
				       ("x"))
     (beta-reduce-antecedent "with(x:ind_1,v:sets[ind_1],  x in v)")
     (instantiate-universal-antecedent "with(p:prop,forall(n_$0:zz,p));"
				       ("n_$0"))
     (contrapose "with(p:prop,not(p));")
     (backchain "with(i,x_$0:ind_2,x_$0=i);")
     (contrapose "with(x:ind_1,f:sets[ind_1],p:prop,x in if(p, f, f));")
     (raise-conditional (0))
     (contrapose "with(p:prop,not(p));")
     (antecedent-inference "with(p:prop,if_form(p, p, p));")
     (contrapose "with(x:ind_1,
  x
   in inv_image{with(f:[ind_1,ind_2],f),
                with(f:sets[ind_2],f)});")
     simplify)
    )))

(def-compound-macete covers-direct-image-to-inverse-image-conversion-macete
  (repeat
   tr%inverse-image-of-finite-covers
   tr%inverse-image-of-covers))

