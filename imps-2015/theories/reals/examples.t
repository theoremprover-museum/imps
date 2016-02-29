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


(herald examples)

(load-section foundation)

(def-theorem exponential-monotonicity-lemma
  "forall(n:zz,2<=n implies (1+1/(n-1))^(n-1)<=(1+1/n)^n)"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "1-1/n<=(1-1/n^2)^n")
    (cut-with-single-formula "n^(2*n)*(n-1)<=n*(n^2-1)^n")
    (weaken (1))
    (cut-with-single-formula "n*(n^2-1)^n=n*(n+1)^n*(n-1)^(n-1)*(n-1)")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (contrapose "with(n:zz,n^(2*n)*(n-1)<=n*(n^2-1)^n);")
    (backchain "with(n:zz,n*(n^2-1)^n=n*(n+1)^n*(n-1)^(n-1)*(n-1));")
    (force-substitution "n^(2*n)" "n^(2*n-1)*n" (0))
    simplify
    simplify
    (apply-macete-with-minor-premises positivity-for-r^n)
    (apply-macete-with-minor-premises positivity-for-r^n)
    simplify
    (cut-with-single-formula "forall(x,y:rr,m:zz,1<=m implies x^m*y^m=(x*y)^m)")
    (backchain "forall(x,y:rr,m:zz,1<=m implies x^m*y^m=(x*y)^m);")
    simplify
    simplify
    (incorporate-antecedent "with(n:zz,1-1/n<=(1-1/n^2)^n);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (apply-macete-with-minor-premises positivity-for-r^n)
    (cut-with-single-formula "1+n*(-1/n^2)<=(1+(-1/n^2))^n")
    simplify
    (apply-macete-with-minor-premises bernoullis-inequality)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (force-substitution "1<n^2" "0<(n-1)*(n+1)" (0))
    (apply-macete-with-minor-premises strict-positivity-for-products)
    simplify
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises positivity-for-r^n)
    simplify

    )))


(def-theorem SUM-LTE-PRODUCT
  "forall(x,y:rr, 2<=x and 2<=y implies x+y<=x*y)"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "1/x+1/y<=1")
    (incorporate-antecedent "with(r:rr,r<=1);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (cut-with-single-formula "1/x<=1/2 and 1/y<=1/2")
    simplify
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    )))

