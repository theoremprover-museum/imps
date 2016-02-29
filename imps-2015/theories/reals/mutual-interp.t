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


(herald mutual-interp)

(load-section reals)

(include-files 
 (files (imps theories/reals/pre-reals)))

;; We prove that complete-ordered-field can be interpreted in h-o-real-arithmetic.
;; The other direction has been established in the file pre-reals.

;;obligations

(def-theorem ()
  "forall(s:[zz,prop],
    forall(t:zz,0<t implies s(t))
     iff 
    (s(1) and forall(t:zz,0<t implies (s(t) implies s(1+t)))))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-inference
    direct-inference
    direct-and-antecedent-inference-strategy
    (backchain "with(s:[zz,prop],forall(t:zz,0<t implies s(t)));")
    simplify
    (backchain "with(s:[zz,prop],forall(t:zz,0<t implies s(t)));")
    simplify
    (cut-with-single-formula "forall(t:zz,1<=t implies s(t))")
    direct-and-antecedent-inference-strategy
    (backchain "with(s:[zz,prop],forall(t:zz,1<=t implies s(t)));")
    simplify
    (induction integer-inductor ("t"))

    )))

(def-theorem ()
  "forall(x:rr,#(x,qq) iff forsome(a,b:zz,x=b^[-1]*a))"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (instantiate-theorem zz-quotient-field ("x"))
    (instantiate-existential ("a" "b"))
    (incorporate-antecedent "with(b,a:zz,x:rr,x=a/b);")
    simplify
    (backchain "with(a,b:zz,x:rr,x=b^[-1]*a);")
    sort-definedness
    (contrapose "with(a,b:zz,x:rr,x=b^[-1]*a);")
    simplify

    )))

(def-theorem ()
  "forall(x:rr,#(x,qq) iff forsome(a,b:zz,x=a*b^[-1]))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
      (instantiate-theorem zz-quotient-field ("x")) (instantiate-existential ("a" "b"))
      (incorporate-antecedent "with(r,x:rr,x=r);") simplify
      )
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
      (backchain "with(p:prop,p);") sort-definedness (contrapose "with(p:prop,p);") simplify
      )    
    )))



(def-theorem ()
  "sub=lambda(x,y:rr,x+[-1]*y)"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    extensionality
    simplify
    )))

(def-theorem ()
  "<= = lambda(x,y:rr,x=y or x<y)"
  (theory h-o-real-arithmetic)
  (proof
   (
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify

    )))
    

(def-theorem ()
  "^
   =lambda(r:rr,n:zz,
      if(n<0, 1/r^(-n), 2<=n, r^n, 1=n, r, not(r=0), 1, ?rr))"
  (theory h-o-real-arithmetic)
  (proof
   (


    extensionality
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (case-split ("x_1<0"))
    (block 
      (script-comment "node added by `case-split' at (1)")
      simplify
      (case-split ("x_0=0"))
      simplify
      simplify)
    (block 
      (script-comment "node added by `case-split' at (2)")
      (case-split ("1=x_1"))
      simplify
      (block 
	(script-comment "node added by `case-split' at (2)")
	(case-split ("2<=x_1"))
	simplify
	(block 
	  (script-comment "node added by `case-split' at (2)")
	  (cut-with-single-formula "x_1=0")
	  (block 
	    (script-comment "node added by `cut-with-single-formula' at (0)")
	    simplify
	    (case-split ("x_0=0"))
	    simplify
	    simplify)
	  simplify)))
    )))


(def-theorem ()
  "forall(h_0:[rr,zz,rr],
    forall(u_0:rr,u_1:zz,
      #(if(u_1<0,
          h_0(u_0,[-1]*u_1)^[-1],
          2<=u_1,
          h_0(u_0,[-1]+u_1)*u_0,
          1=u_1,
          u_0,
          not(u_0=0),
          1,
          ?rr))
       implies 
      if(u_1<0,
        h_0(u_0,[-1]*u_1)^[-1],
        2<=u_1,
        h_0(u_0,[-1]+u_1)*u_0,
        1=u_1,
        u_0,
        not(u_0=0),
        1,
        ?rr)
      =h_0(u_0,u_1))
     implies 
    forall(u_0:rr,u_1:zz,
      #(u_0^u_1) implies u_0^u_1=h_0(u_0,u_1)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "2<=u_1 or 1=u_1 or 0=u_1 or u_1<0")
    (antecedent-inference "with(u_1:zz,2<=u_1 or 1=u_1 or 0=u_1 or u_1<0);")
    (induction trivial-integer-inductor ("u_1"))
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (backchain-backwards "with(p,q:prop,forall(u_0:rr,u_1:zz,p implies q))")
    simplify
    (cut-with-single-formula "u_0^2=h_0(u_0,1)*u_0")
    direct-inference
    (backchain-backwards "with(p,q:prop,forall(u_0:rr,u_1:zz,p implies q))")
    simplify
    (backchain-backwards "with(p,q:prop,forall(u_0:rr,u_1:zz,p implies q))")
    simplify
    (backchain-backwards "with(h_0:[rr,zz,rr],t:zz,u_0:rr,u_0^t=h_0(u_0,t));")
    simplify
    (backchain-backwards "with(p,q:prop,forall(u_0:rr,u_1:zz,p implies q))")
    simplify
    (backchain-backwards "with(p,q:prop,forall(u_0:rr,u_1:zz,p implies q))")
    simplify
    (contrapose "with(u_1:zz,u_0:rr,#(u_0^u_1));")
    simplify
    (cut-with-single-formula "forall(u_1:zz,1<=u_1 implies u_0^u_1=h_0(u_0,u_1))")
    (force-substitution "u_0^u_1" "(u_0^(-u_1))^[-1]" (0))
    (backchain "with(h_0:[rr,zz,rr],u_0:rr,
  forall(u_1:zz,1<=u_1 implies u_0^u_1=h_0(u_0,u_1)));")
    simplify
    (force-substitution "h_0(u_0,[-1]*u_1)^[-1]=h_0(u_0,u_1)"
			"h_0(u_0,u_1)=h_0(u_0,[-1]*u_1)^[-1]" (0))
    (backchain-backwards "with(p,q:prop,forall(u_0:rr,u_1:zz,p implies q))")
    (cut-with-single-formula "not(u_0=0)")
    simplify
    (backchain-backwards "with(h_0:[rr,zz,rr],u_0:rr,
  forall(u_1:zz,1<=u_1 implies u_0^u_1=h_0(u_0,u_1)));")
    simplify
    (contrapose "with(u_1:zz,u_0:rr,#(u_0^u_1));")
    simplify
    simplify
    (cut-with-single-formula "not(u_0=0)")
    simplify
    (weaken (0 1))
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "1=u_1 or 2<=u_1")
    (antecedent-inference "with(u_1:zz,1=u_1 or 2<=u_1);")
    (weaken (1))
    (cut-with-single-formula "#(u_0^u_1)")
    simplify
    (weaken (1))
    (cut-with-single-formula "#(u_0^u_1)")
    simplify
    simplify
    simplify

    )))


(def-translation complete-ordered-field-interpretable
  (source complete-ordered-field)
  (target  h-o-real-arithmetic)
  (constant-pairs 
   (^ ^)
   (sub sub)
   (<= <=))
  (theory-interpretation-check using-simplification))
