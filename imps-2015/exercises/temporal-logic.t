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

;
; 
; 		       TEMPORAL LOGIC EXERCISE
; 
;  			     W. M. Farmer
;   
; 			     1 April 1992
; 
; 
; Temporal logic is a kind of modal logic for reasoning about dynamic
; phenomena.  In recent years temporal logic has won favor as a logic
; for reasoning about programs, particularly concurrent programs.  The
; following is an exercise to develop a version of propositional
; temporal logic (PTL) in IMPS.
; 
; We shall view time as discrete and linear; that is, we shall identify
; time with the integers.  The goal of the exercise is to build
; machinery for reasoning about "time predicates", which are simply
; expressions of sort [zz -> prop].  In traditional PTL, the time
; argument is suppressed and formulas are manipulated instead of
; predicates.  In IMPS we will deal directly with predicates, which has
; several advantages.


; STEP 1: Formalize the basic operators of PTL in the theory
;         H-O-REAL-ARITHMETIC.
; 
; PTL has two kinds of operators:
; 
;   1. Propositional connectives: t%true, t%false, t%not, t%and, t%or.
; 
;   2. Modal operators: t%nec, t%pos, t%next, t%unless, t%prec.
; 
; The meaning of the modal operators is as follows:
; 
;   t%nec(p)(n)      means  (forall m >= n, p(m)) holds.
; 
;   t%pos(p)(n)      means  (forsome m >= n, p(m)) holds.
;   
;   t%next(p)(n)     means  p(n+1) holds.
;   
;   t%unless(p,q)(n) means 
; 
;     (forall m >= n, p(m) or (forsome k with n<=k<=m, q(k))).
; 
;   t%prec(p,q)(n)   means
; 
;     (forsome m >= n, p(m) and (forall k with n<=k<=m, not q(k))).
; 
; The definitions of the operators are very straightforward; e.g.,
; t%true, t%and, and t%nec are defined as follows:

(def-constant T%TRUE
  "lambda(n:nn, truth)"
  (theory h-o-real-arithmetic))

(def-constant T%AND
  "lambda(p,q:[nn -> prop], lambda(n:nn, p(n) and q(n)))"
  (theory h-o-real-arithmetic))

(def-constant T%NEC
  "lambda(p:[nn -> prop], 
     lambda(n:nn, forall(m:nn, m >= n implies p(m))))"
  (theory h-o-real-arithmetic))

; Define the other operators.
 

; STEP 2: Prove the following sentences and install them in
;         H-O-REAL-ARITHMETIC as rewrite rules.

  "t%not(t%true) = t%false"
  "t%not(t%false) = t%true"
  "t%and(t%true,t%true) = t%true"
;    etc.

  "t%nec(t%true) = t%true"
  "t%nec(t%false) = t%false"

  "t%pos(t%true) = t%true"
  "t%pos(t%false) = t%false"

  "t%next(t%true) = t%true"
  "t%next(t%false) = t%false"

  "forall(p:[zz -> prop], t%unless(t%true,p) = t%true)"
  "forall(p:[zz -> prop], t%unless(p,t%true) = t%true)"
  "forall(p:[zz -> prop], t%unless(t%false,p) = p)"

  "forall(p:[zz -> prop], t%prec(t%true,p) = t%not(p))"
  "forall(p:[zz -> prop], t%prec(p,t%true) = t%false)"
  "forall(p:[zz -> prop], t%prec(t%false,p) = t%false)"

 
; STEP 3: Prove the following sentences and install them in
;         H-O-REAL-ARITHMETIC.  Then build a "push-t%not" macete 
;         from them.

  "forall(p:[zz -> prop], t%not(t%not(p)) = p)"
  "forall(p,q:[zz -> prop], 
     t%not(t%and(p,q)) = t%or(t%not(p),t%not(q)))"
  "forall(p,q:[zz -> prop], 
     t%not(t%or(p,q)) = t%and(t%not(p),t%not(q)))"
  "forall(p:[zz -> prop], t%not(t%nec(p)) = t%pos(t%not(p)))"
  "forall(p:[zz -> prop], t%not(t%pos(p)) = t%pos(t%nec(p)))"
  "forall(p:[zz -> prop], t%not(t%next(p)) = t%next(t%not(p)))"
  "forall(p,q:[zz -> prop], 
     t%not(t%unless(p,q)) = t%prec(t%not(p),q))"
  "forall(p,q:[zz -> prop], 
     t%not(t%prec(p,q)) = t%unless(t%not(p),q))"

 
; STEP 4: Prove the following modality rules and install them in 
;         H-O-REAL-ARITHMETIC.  

; t%nec-rule:
  "forall(p:[zz -> prop], 
     t%nec(p)=t%true implies t%and(p,t%next(t%nec(p)))=t%true)"

; t%pos-rule:
  "forall(p:[zz -> prop], 
     t%pos(p)=t%true implies t%or(p,t%next(t%pos(p)))=t%true)"

; t%nec-t%nec-rule:
  "forall(p,q:[zz -> prop], 
     t%nec(p)=t%true and t%nec(q)=t%true 
      implies 
     t%nec(t%and(t%nec(p),q))=t%true)"

; t%nec-t%pos-rule:
  "forall(p,q:[zz -> prop], 
     t%nec(p)=t%true and t%pos(q)=t%true
      implies 
     t%pos(t%and(t%nec(p),q))=t%true)"

; t%pos-t%pos-rule:
  "forall(p,q:[zz -> prop], 
     t%pos(p)=t%true and t%pos(q)=t%true 
      implies 
     t%or(t%pos(t%and(p,t%pos(q))),t%pos(t%and(t%pos(p),q)))=t%true)"

; t%next-t%next-rule:
  "forall(p,q:[zz -> prop], 
     t%next(p)=t%true and t%next(q)=t%true 
      implies 
     t%next(t%and(p,q))=t%true)"

; t%nec-t%next-rule:
  "forall(p,q:[zz -> prop], 
     t%nec(p)=t%true and t%next(q)=t%true 
      implies 
     t%next(t%and(t%nec(p),q))=t%true)"

; t%pos-t%next-rule:
  "forall(p,q:[zz -> prop], 
     t%pos(p)=t%true and t%next(q)=t%true 
      implies 
     t%or(p,t%next(t%and(t%pos(p),q))=t%true)"

 
; STEP 5: To test the machinery we have developed to this point, prove
;         the following theorem:

  "forall(p:[zz -> prop], 
     t%or(t%nec(t%pos(p)),
       t%not(t%and(p,t%or(t%not(p),t%next(t%pos(p))))))
        =
       t%true)"

 
; STEP 6: Prove and install the following induction principle:

  "forall(p,q:[zz -> prop],
     t%not(t%and(p,q))=t%true and p=t%true and t%pos(q)=t%true
      implies
     t%pos(t%and(t%not(p),t%next(t%and(p,t%not(q)))))=t%true)"

;
; 			   END OF EXERCISE

