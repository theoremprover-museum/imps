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


(herald PURE-GENERIC-THEORIES)

;;; No required files


;;; The kernel translation

(def-translation THE-KERNEL-TRANSLATION
  (source the-kernel-theory)
  (target the-kernel-theory))

(define the-kernel-translation (name->translation 'the-kernel-translation))


;;; Build pure generic theories

(def-language PURE-GENERIC-LANGUAGE-1
  (base-types ind_1))

(def-language PURE-GENERIC-LANGUAGE-2
  (embedded-language pure-generic-language-1)
  (base-types ind_2))

(def-language PURE-GENERIC-LANGUAGE-3
  (embedded-language pure-generic-language-2)
  (base-types ind_3))

(def-language PURE-GENERIC-LANGUAGE-4
  (embedded-language pure-generic-language-3)
  (base-types ind_4))

(def-theory PURE-GENERIC-THEORY-0)

(define pure-generic-theory-0 (name->theory 'pure-generic-theory-0))

(def-theory PURE-GENERIC-THEORY-1
  (language pure-generic-language-1)
  (component-theories pure-generic-theory-0))

(define pure-generic-theory-1 (name->theory 'pure-generic-theory-1))

(def-theory PURE-GENERIC-THEORY-2
  (language pure-generic-language-2)
  (component-theories pure-generic-theory-1))

(define pure-generic-theory-2 (name->theory 'pure-generic-theory-2))

(def-theory PURE-GENERIC-THEORY-3
  (language pure-generic-language-3)
  (component-theories pure-generic-theory-2))

(define pure-generic-theory-3 (name->theory 'pure-generic-theory-3))

(def-theory PURE-GENERIC-THEORY-4
  (language pure-generic-language-4)
  (component-theories pure-generic-theory-3))

(define pure-generic-theory-4 (name->theory 'pure-generic-theory-4))


;;; Dangling conditionals

(def-theorem DEFINEDNESS-OF-DANGLING-CONDITIONALS
  "forall(a:prop,b:ind_1, #(if(a,b,?ind_1)) iff a)"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof (simplify)))



