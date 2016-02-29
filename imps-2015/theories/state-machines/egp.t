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


(herald egp)

(*require nil '(theories state-machines/tabular) imps-implementation-env)
(*require nil '(theories state-machines/deterministic-state-machines) imps-implementation-env)


(push-current-theory)

(language-from-definition
 '(egp-machine-language
   (base-types state action)
   
   (constants
    (up%action action)
    (down%action action)
    (request action)
    (refuse action)
    (confirm action)
    (cease%action action)
    (cease%ack action)
    (hello action)
    (i%h%u action)
    (poll action)
    (update action)
    (start action)
    (stop%t3 action)
    (t1 action)
    (t2 action)
    (eps action)

    (process action)

    (idle state)
    (aqsn state)
    (down%state state)
    (up%state state)
    (cease%state state)

    (next (action state state))
    (output (action state action))
    (internal (action state action)))))

(define egp-state-machine
  (theory-from-definition
   '(egp-state-machine
     (language egp-machine-language)
     (component-theories h-o-real-arithmetic)
     (distinct-constants 
      (up%action
      down%action
      request
      refuse
      confirm
      cease%action
      cease%ack
      hello
      i%h%u
      poll
      update
      start
      stop%t3
      t1
      t2
      eps
      process
      idle 
      aqsn 
      down%state 
      up%state 
      cease%state))

     (axioms
      (action-cases
       "forall(x:action, x=up%action or x=down%action or x=request or x=confirm or x=refuse or x=cease%action or x=cease%ack or x=hello or x=i%h%u or x=poll or x=update or x=start or x=stop%t3 or x=t1 or x=t2)" ())
      (state-cases "forall(x:state, x=idle or x=aqsn or x=down%state or x=up%state or x=cease%state)" ())
      (egp_state_table
       "table (next,
          {up%action,down%action,request,confirm,refuse,cease%action,cease%ack,hello,i%h%u,poll,update,start,stop%t3,t1,t2},          
          {idle,aqsn,down%state,up%state,cease%state},
          {idle,aqsn,up%state,up%state,cease%state},
          {idle,aqsn,down%state,down%state,cease%state},
          {down%state,down%state,down%state,down%state,cease%state},
          {idle,down%state,down%state,up%state,cease%state},
          {idle,idle,down%state,up%state,cease%state},
          {idle,idle,idle,idle,idle},
          {idle,aqsn,down%state,up%state,idle},
          {idle,aqsn,down%state,up%state,cease%state},
          {idle,aqsn,down%state,up%state,cease%state},
          {idle,aqsn,down%state,up%state,cease%state},
          {idle,aqsn,down%state,up%state,cease%state},
          {aqsn,aqsn,aqsn,aqsn,cease%state},
          {idle,idle,cease%state,cease%state,idle},
          {idle,aqsn,down%state,up%state,cease%state},
          {idle,aqsn,down%state,up%state,cease%state})"
       (rewrite))
      
      (egp_output_table
       "table (output,{up%action,down%action,request,confirm,refuse,cease%action,cease%ack,hello,i%h%u,poll,update,start,stop%t3,t1,t2},          
          {idle,aqsn,down%state,up%state,cease%state},
          {eps,eps,poll,eps,eps},
          {eps,eps,eps,eps,eps},
          {confirm,confirm,confirm,confirm,cease%action},
          {cease%action,eps,eps,eps,eps},
          {cease%action,eps,eps,eps,eps},
          {cease%ack,cease%ack,cease%ack,cease%ack,cease%ack},
          {eps,eps,eps,eps,eps},
          {cease%action,eps,i%h%u,i%h%u,eps},
          {cease%action,eps,process,process,eps},
          {cease%action,eps,eps,update,eps},
          {cease%action,eps,eps,process,eps},
          {request,request,request,request,eps},
          {eps,eps,cease%action,cease%action,eps},
          {eps,request,hello,hello,cease%action},
          {eps,eps,eps,poll,eps})"
       (rewrite))))))

(theory-import-transportable-rewrite-rules egp-state-machine (list sequences))

(set (current-theory) egp-state-machine)

(lset deterministic-state-machine-to-egp
      (translation-from-definition
       '(deterministic-state-machine-to-egp
	 (source det-state-machines)
	 (target egp-state-machine)
	 (fixed-theories h-o-real-arithmetic)
	 (sort-pairs
	  (state state) (action action))
	 (constant-pairs
	  (initial "lambda(x:state,x=down%state)")
	  (accepting "lambda(x:state,falsehood)")
	  (tr "lambda(s:state,a:action,s1:state,next(a,s) = s1)")
	  (next "lambda(s:state,a:action,next(a,s))")))))

(theory-interpretation-check-using-simplification
 deterministic-state-machine-to-egp)

;(transport-defined-constants
; 'deterministic-state-machine-to-egp
; '(run) '(egp%run))

(def-transported-symbols run
  (translation deterministic-state-machine-to-egp))

(pop-current-theory)
