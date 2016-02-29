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



; This is the set-up file for the micro exercises described in the
; IMPS user's manual.
;

(load-section foundation)

(def-theorem factorial-of-zero
  "0!=1"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally factorial)
    (unfold-single-defined-constant-globally prod)
    simplify

    )))

(def-theorem factorial-of-nonpositive
  "forall(j:zz, j<=0 implies j!=1)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally factorial)
    (unfold-single-defined-constant-globally prod)
    simplify

    )))

(def-compound-macete factorial-reduction
  (repeat 
   (without-minor-premises
    (repeat factorial-out factorial-of-nonpositive))
   simplify))

(def-script comb-ident-script 0
  ((unfold-single-defined-constant-globally comb)
   (apply-macete-with-minor-premises fractional-expression-manipulation)
   (label-node compound)
   direct-and-antecedent-inference-strategy
   (jump-to-node compound)
   (for-nodes
    (unsupported-descendents)
    (if (matches? "with(t:rr, #(t^[-1]))")
	(apply-macete-with-minor-premises definedness-manipulations)
	(block
	  (apply-macete-with-minor-premises factorial-reduction)
	  simplify)))))

(lset comb-ident
      "forall(k,m:zz,
         1<=k and k<=m implies comb(1+m,k)=comb(m,k-1)+comb(m,k))") 

(lset 1stn
      "forall(m:zz,
         0<=m implies sum(0,m,lambda(j:zz,j))=m*((m+1)/2))")

(def-compound-macete little-integer-induction 
  (sequential
   (sound
    abstraction-for-induction
    beta-reduce
    beta-reduce)
   induct
   beta-reduce-repeatedly))
