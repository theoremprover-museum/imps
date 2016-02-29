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


(herald vector-spaces)

(include-files 
 (files (imps theories/algebra/fields)))


;;; Vector spaces

(def-language VECTOR-SPACE-LANGUAGE 
  (base-types vv)
  (embedded-languages fields)
  (constants
   (++ (vv vv vv))
   (v0 vv)
   (** (kk vv vv))))

(def-theory VECTOR-SPACES
  (language vector-space-language)
  (component-theories fields h-o-real-arithmetic)
  (axioms
   (vector-plus-totality
    "total_q{++,[vv, vv, vv]}" d-r-convergence transportable-macete)
   (vector-plus-associativity
    "forall(x,y,z:vv, (x ++ y) ++ z = x ++ (y ++ z))" transportable-macete)
   (vector-plus-commutativity
    "forall(x,y:vv, x ++ y  =  y ++ x)" transportable-macete)
   (vector-zero-identity
    "forall(x:vv, x ++ v0=x)" transportable-macete)
   (vector-times-totality
    "total_q{**,[kk, vv, vv]}" d-r-convergence transportable-macete)
   (vector-times-associativity
    "forall(x,y:kk, z:vv, (x *_kk y)**z = x ** (y ** z))" transportable-macete)
   (vector-times-left-distributivity
    "forall(x,y:vv, a:kk, a ** (x ++ y) = (a**x) ++ (a**y))" transportable-macete)
   (vector-times-right-distributivity
    "forall(a,b:kk, x:vv, (a +_kk b)**x = (a**x) ++ (b**x))" transportable-macete)
   (scalar-multiplication-by-zero
    "forall(x:vv, o_kk ** x = v0)" transportable-macete)
   (scalar-multiplication-by-one
    "forall(x:vv, i_kk ** x = x)" transportable-macete)))

(make-tex-correspondence "vv" " \{ \\bf V \}")

