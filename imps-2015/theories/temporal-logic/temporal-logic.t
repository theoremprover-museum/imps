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


(herald TEMPORAL-LOGIC)

(load-section foundation)

;;; Definitions of PTL operators

(def-constant T%TRUE
  "lambda(n:nn, truth)"
  (theory h-o-real-arithmetic))

(def-constant T%FALSE
  "lambda(n:nn, falsehood)"
  (theory h-o-real-arithmetic))

(def-constant T%NOT
  "lambda(f:[nn,prop], lambda(n:nn, not(f(n))))"
  (theory h-o-real-arithmetic))

(def-constant T%AND
  "lambda(f,g:[nn,prop], lambda(n:nn, f(n) and g(n)))"
  (theory h-o-real-arithmetic))

(def-constant T%OR
  "lambda(f,g:[nn,prop], lambda(n:nn, f(n) or g(n)))"
  (theory h-o-real-arithmetic))

(def-constant T%NEC
  "lambda(f:[nn,prop], lambda(n:nn, forall(i:nn, n<=i implies f(i))))"
  (theory h-o-real-arithmetic))

(def-constant T%POS
  "lambda(f:[nn,prop], lambda(n:nn, forsome(i:nn, n<=i implies f(i))))"
  (theory h-o-real-arithmetic))

(def-constant T%NEXT
  "lambda(f:[nn,prop], lambda(n:nn, f(n+1)))"
  (theory h-o-real-arithmetic))

(def-constant T%UNLESS
  "lambda(f,g:[nn,prop], 
     lambda(n:nn, 
       forall(i:nn, f(i) 
         or 
       forsome(j:nn, n<=j and j<=i and g(i)))))"
  (theory h-o-real-arithmetic))

(def-constant T%PREC
  "lambda(f,g:[nn,prop], 
     lambda(n:nn, 
       forsome(i:nn, f(i) 
         and 
       forall(j:nn, n<=j and j<=i implies not(g(i))))))"
  (theory h-o-real-arithmetic))


;;; Rewrite rules

(def-theorem T%NEC-T%TRUE-REWRITE
  "t%nec(t%true) = t%true"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-theorem T%NEC-T%FALSE-REWRITE
  "t%nec(t%false) = t%false"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-theorem T%POS-T%TRUE-REWRITE
  "t%pos(t%true) = t%true"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-theorem T%POS-T%FALSE-REWRITE
  "t%pos(t%false) = t%false"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-theorem T%NEXT-T%TRUE-REWRITE
  "t%next(t%true) = t%true"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-theorem T%NEXT-T%FALSE-REWRITE
  "t%next(t%false) = t%false"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-theorem T%UNLESS-T%TRUE-P-REWRITE
  "forall(p:[zz,prop], t%unless(t%true,p) = t%true)"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-theorem T%UNLESS-P-T%TRUE-REWRITE
  "forall(p:[zz,prop], t%unless(p,t%true) = t%true)"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-theorem T%UNLESS-T%FALSE-P-REWRITE
  "forall(p:[zz,prop], t%unless(t%false,p) = p)"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-theorem T%PREC-T%TRUE-P-REWRITE
  "forall(p:[zz,prop], t%prec(t%true,p) =$ t%not(p))"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-theorem T%PREC-P-T%TRUE-REWRITE
  "forall(p:[zz,prop], t%prec(p,t%true) = t%false)"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-theorem T%PREC-T%FALSE-P-REWRITE
  "forall(p:[zz,prop], t%prec(t%false,p) = t%false)"
  (theory h-o-real-arithmetic)
  (usages rewrite))



