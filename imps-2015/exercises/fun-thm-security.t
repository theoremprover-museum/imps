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

;  In this file we prove the Bell-LaPadula fundamental theorem of security.
;  This theorem justifies the inductive state machine approach to proving
;  system security.  We will later apply this general theory to a concrete
;  theory about a state machine with four "user-commands" to:
;
;  get/delete access to a file for read/write.  
;
;  The first thing we must do is to load in the theory of
;  determinsitic state machines.   

(load-section sequences)

(*require
 nil
 '(theories state-machines/deterministic-state-machines)
 imps-implementation-env)

;  We extend the language of deterministic state machines (with a unique start
;  state) to contain a new (unconstrained) predicate of states, intended to
;  represent the property of being secure.  The fts-theory is simply the theory
;  of a deterministic state machine (with a unique start state) in the extended
;  language.

(def-language fts-language
  (embedded-language det-state-machines-with-start)
  (constants 
   (secure%state (state prop))))

(def-theory fts-theory
  (language fts-language)
  (component-theories det-state-machines-with-start))

(set (current-theory) (name->theory 'fts-theory))

;; The first candidate theorem justifies the method.  Prove it by induction for
;; deterministic state machines (dsm).  

(def-theorem fun-sec
  "secure%state(s_init) 
      and
     forall(s:state,a:action, 
	secure%state(s) and #(next(s,a))
       implies secure%state(next(s,a)))
   implies forall(s:state, accessible(s) implies secure%state(s)) "
  (theory fts-theory)
  (proof ((induction dsm-inductor ("s")))))

;; Here we define an extended theory with AXIOMS stating that the  initial
;; state is secure and that (defined) transitions preserve security.  This is
;; desirable, because when we prove that a concrete is an instance of
;; fts+invariant, then we can apply the simpler form of the fundamental
;; security theorem given below as a "transportable macete".  

(def-theory fts+invariant
  (component-theories fts-theory)
  (axioms
   (fts+init-secure "secure%state(s_init)" rewrite)
   (fts+next-secure
      "forall(s:state,a:action, 
	secure%state(s) and #(next(s,a))
       implies secure%state(next(s,a)))")))
      
(set (current-theory) (name->theory 'fts+invariant))

;; To prove this, apply fun-sec as a macete.  Then use fts+next-secure as a
;; macete.  Simplification completes the proof.  

(def-theorem fts+secure
  "forall(s:state, accessible(s) implies secure%state(s))"
  (theory fts+invariant)
  (usages transportable-macete)
  (proof ((apply-macete-with-minor-premises fun-sec)
	  (apply-macete-with-minor-premises fts+init-secure)
	  (apply-macete-with-minor-premises fts+next-secure))))
