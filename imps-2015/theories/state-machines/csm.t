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


(herald csm)

(*require nil '(theories state-machines/hoare-machines) imps-implementation-env)
(*require nil '(generic_theories pairs) imps-implementation-env)
(push-current-theory)
(push-current-syntax)

(set (use-string-form?) '#t)

(def-language csm-0-language
  (base-types channel message))

(def-theory csm-0-theory
  (language csm-0-language)
  (component-theories h-o-real-arithmetic the-kernel-theory))

(def-cartesian-product action
  (port message)
  (accessors channel message)
  (constructor build%action)
  (theory port-theory))

(def-language port-language
  (embedded-language csm-0-language)
  (sorts (port channel)))

(def-theory port-theory
  (language port-language)
  (component-theories csm-0-theory))

(def-parse-syntax build%action
  (token @)
  (left-method infix-operator-method)
  (binding 180))

(def-print-syntax build%action
  (token " @ ")
  (method present-binary-infix-operator) 
  (binding 180))

(def-imported-rewrite-rules port-theory
  (source-theories pairs sequences))

(def-language csm-language
  (embedded-language port-theory)
  (base-types state)
  (constants 
   (next (state action state))
   (initial (state prop))))

(def-theory csm-theory
  (component-theories h-o-real-arithmetic)
  (language csm-language))

(def-theory-ensemble-instances det-hoare-machines
  (target-theories csm-theory)
  (sorts 
   (state state)
   (action action))
  (constants
   (next  next)
   (initial initial))
  (multiples 1))

(def-theory-ensemble csm-theory
  (fixed-theories csm-0-theory))

(def-theory-ensemble-multiple csm-theory 3 (fixed-theories csm-0-theory))

(def-theory-ensemble-overloadings csm-theory (1) (fixed-theories csm-0-theory))


(def-cartesian-product composite%state
  (state_0 state_1 state_2)
  (constructor build%composite%state)
  (accessors component_0 component_1 component_2)
  (theory csm-theory-3-tuples))



