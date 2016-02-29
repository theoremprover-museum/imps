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


(herald fun-thm-security)


(*require
 nil '(theories state-machines/deterministic-state-machines) imps-implementation-env)

(push-current-theory)
(push-current-syntax)
(set (use-string-form?) '#t)

(def-language fts-language
  (embedded-language det-state-machines-with-start)
  (constants 
   (secure%state (state prop))))

(def-theory fts-theory
  (language fts-language)
  (component-theories det-state-machines-with-start))

(set (current-theory) (name->theory 'fts-theory))

;; First candidate theorem justifies the method.

(def-theorem fun-sec
  "secure%state(s_init) 
      and
     forall(s:state,a:action, 
	secure%state(s) and #(next(s,a))
       implies secure%state(next(s,a)))
   implies forall(s:state, accessible(s) implies secure%state(s)) "
  (theory fts-theory)
  (proof "$THEORIES/state-machines/proofs/fun-sec.t"))

(def-theory fts+invariant
  (component-theories fts-theory)
  (axioms
   (fts+init-secure "secure%state(s_init)" rewrite)
   (fts+next-secure
      "forall(s:state,a:action, 
	secure%state(s) and #(next(s,a))
       implies secure%state(next(s,a)))")))
      
(def-theorem fts+secure
  "forall(s:state, accessible(s) implies secure%state(s))"
  (theory fts+invariant)
  (usages transportable-macete)
  (proof "$THEORIES/state-machines/proofs/fts+secure.t.Z"))
  
  


(pop-current-theory)
(pop-current-syntax)

