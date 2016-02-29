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


;; (herald bell-lapadula)

;; You must first have loaded the file $IMPS/theories/exercises/fun-thm-security.t: 

(*require nil '(theories exercises/fun-thm-security) imps-implementation-env)

;; Suppose now that we want to introduce a particular notion of secure%state,
;; and thus also to commit ourselves to a particular notion of state.  For this
;; version, we will suppose that there is a fixed function that associates a
;; level with each subject and object.  The main security theorem asserts:
 
;; (def-theorem bell_lapadula-security 
;;   "forall(s:state, accessible(s) implies secure%state(s))"
;;   (theory action_records))

;; That is, we're using the traditional Bell-LaPadula idea that a secure system
;; is one in which there is a notion of secure state, and moreover every state
;; that the system can actually enter is a secure state in that sense.  

;; We will actually introduce the state machine apparatus only quite late in
;; this file, by means of the form

;; (def-theory-ensemble-instances
;;   det-state-machines-with-start
;;   (target-theories action_records)
;;   (sorts (state state) (action action))
;;   (multiples 1)
;;   (theory-interpretation-check using-simplification)
;;   (constants
;;    (next next)
;;    (tr "lambda(s:state, a:action, s_1:state, next(s,a)=s_1)")
;;    (initial "lambda(f:state, f=s_init)")
;;    (s_init s_init)
;;    (accepting "lambda(f:state, falsehood)")))

;; Ignoring the difference between a theory ensemble and an ordinary theory,
;; which is irrelevant in this case, what this form does is to declare that we
;; will regard the theory action_records as an instance of the general theory
;; of deterministic state machines with a distinguished start state.  It says
;; that the transition function "next" of the general theory of deterministic
;; state machines will be associated with the action_records function that
;; happens to be called "next", etc.  It is not important to know the details of
;; the general state machine theories.

;; The state is a FUNCTION.  Given two arguments, namely a subject and an
;; argument, it returns a set of accesses.  Thus, it represents the familiar
;; access control matrix (regarding a matrix as a two-place function).  A state
;; is secure if for every subject/object pair, the simple security and star
;; property hold of the access set.  In the initial state, the access set is
;; null.

;; The theory concerns two basic types.  First are the "users" and "objects"
;; (e.g. files) of the system, which we call jointly "entities."  It is not
;; assumed that the users and objects are disjoint, although in many further
;; applications of the theory they would be.  Next come the security levels
;; themselves, about which we assume that they are equipped with a partial
;; order leq.  level%of is a total function mapping entities to levels.

(def-language entities-and-levels-language
  (base-types entity level)
  (sorts (object entity)
	 (user   entity))
  (constants
   (level%of (entity level))
   (leq (level level prop))))

(def-theory entities-and-levels
  (language entities-and-levels-language)
  (axioms
   (level%of-total
    "total_q{level%of,[entity,level]}"
    d-r-convergence)
   (leq-reflexive
    "forall(l_0:level, leq(l_0, l_0))"
    rewrite)
   (leq-antisymmetric
    "forall(l_0,l_1:level, leq(l_0, l_1) and leq(l_1, l_0) implies l_0=l_1)"
    ())
   (leq-transitive
    "forall(l_0,l_1,l_2:level, leq(l_0, l_1) and leq(l_1, l_2) implies leq(l_0, l_2))"
    ())))

;; The next form defines a theory ACCESS_RECORDS that extends
;; entities-and-levels.  It contains a new base type ACCESS.  An access is a
;; record structure with a read field and a write field (each either true or
;; false).  The selectors will be access_read and access_write.  The usual
;; data-type no-junk and no-confusion axioms are included, as well as rewrite
;; rules access_read(make_access(p,q))=p and access_write(make_access(p,q))=q.
;; This is not yet available through a def-form.

(define access_records
  (make-record-theory-with-sortnames
   (name->theory 'entities-and-levels)
   'access
   '((read "prop")
     (write "prop"))))

(set (current-theory) access_records)
(def-imported-rewrite-rules access_records
  (source-theories family-indicators))


;; Here are some definitions that introduce an initial state, and a subtype of
;; consisting of the possible states.  These states are really functions: When
;; given a user and an object, a state returns an access.  The only condition
;; for a function to be in the subtype is that is should be total (for users
;; and objects).

(def-constant empty%access
  "make_access(falsehood,falsehood)"
  (theory access_records))

;; The initial state of our machine contains no access rights for any
;; user-object pair.    

(def-constant s_init
  "lambda(u:user,o:object, empty%access)"
  (theory access_records))

;; We note that this is a total function:  

(def-theorem s_init-is-total
  "total_q{s_init,[user,object,access]}"
  (theory access_records)
  (usages d-r-convergence)
  ;; Unfold the definition and simplify-insistently 
  (proof ((unfold-single-defined-constant (0) s_init)
	  simplify-insistently)))

;; Now we define the states to be those functions (of this sort) that are
;; total.  Since in the Imps logic, every sort must be non-empty, we supply a
;; witness, namely s_init, which we have just shown to meet this condition.  

(def-atomic-sort state
  "lambda(f:[user,object,access], total_q{f,[user,object,access]})"
  (theory access_records)
  (witness "s_init")
  (usages rewrite))

;; For future convenience we install the fact that s_init is a state as a
;; rewrite.  To prove it, use the macetes available on the macete menu: first
;; state-defining-axiom_access_records, then s_init-is-total.  

(def-theorem s_init-is-state
  "#(s_init,state);"
  (theory access_records)
  (usages rewrite)
  (proof ((apply-macete-with-minor-premises state-defining-axiom_access_records)
	  simplify
	  (apply-macete-with-minor-premises s_init-is-total))))

;; We next establish the duality of read and write.  We do this by supplying a
;; theory interpretation: it interchanges read and write, and inverts the sense
;; of the partial ordering.  It is very useful, as we can prove a theorem about
;; read, and then get the dual theorem about write "for free", using the
;; interpretation.

;; Four obligations must be proved to justify the translation (i.e.  to
;; establish that it is a theory-interpretation).  They are not interesting,
;; and are easy to prove.  They are contained in the file
;; $IMPS/theories/state-machines/bl-exercise-obligations.t
;; The keyword FORCE below tells Imps not to bother about them.   It should be
;; used only when the obligations have been proved and stored in a file.  

(def-translation access_records-symmetry
  force 
  (source access_records)
  (target access_records)
  (sort-pairs (state state))
  (constant-pairs
   (leq					; Invert the ordering 
    "lambda(l_0,l_1:level, leq(l_1,l_0))")		
   (make_access				; Interchange read and write slots 
    "lambda(write,read:prop, 
	make_access(read, write))")
   (access_read access_write)		; map read to write 
   (access_write access_read))		; map write to read 
  (theory-interpretation-check using-simplification))

; SIMPLY%SECURE contains the real content of the notion of secure state in this
; exercise.  A state will be defined to be secure if it has both this and the
; dual property.  Its content is just that if you can read the file, then your
; level dominates its level.   

(def-constant simply%secure
  "lambda(f:state, 
	forall(u:user,o:object, 
	   access_read(f(u,o)) implies leq(level%of(o),level%of(u))))"
  (theory access_records))

;; Here follow two auxiliary definitions, and then the definitions of two of
;; the four state changing operations.  There will be four in all, with the
;; other two being the duals of these two.  With%read%access updates
;; access_read in an access to be true, and without%read%access makes it
;; false.       

(def-constant with%read%access
  "lambda(a:access, make_access(truth,access_write(a)))"
  (theory access_records))

(def-constant without%read%access
  "lambda(a:access, make_access(falsehood,access_write(a)))"
  (theory access_records))

;; State-changing operation to get read access to an object:

(def-constant get%read%access
 "lambda(s:state, u:user, o:object, 
	if(leq(level%of(o), level%of(u)),
	   lambda(u_0:user, o_0:object,
	     if(u=u_0 and o=o_0, with%read%access(s(u,o)), s(u_0,o_0))),
	   s))"
  (theory access_records))

;; State-changing operation to relinquish read access to an object:

(def-constant del%read%access
  "lambda(s:state, u_0:user, o_0:object, 
	lambda(u:user, o:object, if(u=u_0 and o=o_0, without%read%access(s(u,o)), s(u,o))))"
  (theory access_records))

;; Now please load six slightly boring lemmas from an auxiliary file.  They are
;; not hard to prove, but they distract from the main line of the exercise.
;; You may look at them in $IMPS/theories/exercises/aux-bell-lapadula.t if
;; you're interested.  

(load '(theories exercises/aux-bell-lapadula) imps-implementation-env)

;; Here is a series of "security relevant lemmas".  The first asserts that
;; write is irrelevant to simple security.  To prove it, use the command
;; unfold-defined-constants, and then simplify.

(def-theorem simple%security-depends-on-read
  "forall(s_0,s_1:state, 
	forall(u:user, o:object, access_read(s_0(u,o))=access_read(s_1(u,o)))
       implies
	simply%secure(s_0) iff simply%secure(s_1))"
  (theory access_records)
  (usages )
  (proof ((unfold-single-defined-constant-globally simply%secure)
	  (prove-by-logic-and-simplification 0)))) 

;; The next asserts that get%read doesn't affect write.  To prove it,
;; unfold-defined-constants twice, do one direct inference, and then use
;; case-split-on-conditionals twice.

(def-theorem get%read-leaves-write-unchanged
 "forall(s:state,u,u_0:user, o,o_0:object,
	 access_write(get%read%access(s,u_0,o_0)(u,o))=access_write(s(u,o)))"
 (theory access_records)
 (usages )
 (proof ((unfold-single-defined-constant-globally get%read%access)
	 (raise-conditional (0))
	 (unfold-single-defined-constant-globally with%read%access)
	 (raise-conditional (0))
	 (prove-by-logic-and-simplification 1)))) 

;; Next comes the crucial security relevant fact that get%read%access
;; preserves simple security.  The proof goes as follows:  
;;
;; 1.  Unfold the definition of simply%secure.
;; 2.  Simplify
;; 3.  Unfold the definition of get%read%access.
;; 4.  Type capital D, for direct-and-antecedent-inference-strategy.
;; 5.  At the NEXT TO LAST node, do case-split-on-conditionals 0.
;; 6.  At the ungrounded subgoal, do case-split-on-conditionals 0 again.
;;
;; At step 5., the last node has the conditional in the context, rather
;; than in the assertion, where we can't exploit it as easily.

(def-theorem get%read-preserves-simple-security
 "forall(s:state,u:user,o:object, 
   simply%secure(s) 
  implies
  simply%secure(get%read%access(s,u,o)));" 
 (theory access_records)
  (usages )
 (proof ((unfold-single-defined-constant-globally simply%secure)
	 simplify
	 (unfold-single-defined-constant-globally get%read%access)
	 (raise-conditional (0))
	 simplify
	 (raise-conditional (0))
	 direct-and-antecedent-inference-strategy-with-simplification))) 

;; Here are the corresponding theorems for del%read%access.  Proofs are
;; similar.  You will probably want to skip the proofs and simply evaluate
;; the forms.

(def-theorem del%read-preserves-simply%secure
  "forall(s:state, u:user, o:object, 
	simply%secure(s)
       implies
 	simply%secure(del%read%access(s,u,o)))" 
  (theory access_records)
  (usages )
  (proof (
	  (unfold-single-defined-constant-globally simply%secure)
	  simplify
	  (unfold-single-defined-constant-globally del%read%access)
	  (raise-conditional (0))
	  (unfold-single-defined-constant-globally without%read%access)
	  simplify)))

(def-theorem del%read-leaves-write-unchanged
  "forall(s:state,u,u_0:user, o,o_0:object,
	 access_write(del%read%access(s,u_0,o_0)(u,o))=access_write(s(u,o)))" 
  (theory access_records)
  (usages )
  ;; eliminate-definitions-and-simplify, d, case-split-on-conditionals.
  (proof ((unfold-single-defined-constant-globally del%read%access)
	  (unfold-single-defined-constant-globally without%read%access)
	  (raise-conditional (0))
	  simplify)))

;; Lo!  A Hack!  The following procedure does renaming to apply our
;; symmetry interpretation to all the new constants.  It will rename
;; someting SIMPLE to something STAR, etc.  

(define second-bl-renamer
  (compose (replace-substring-renamer "SIMPLE" "STAR")
	   (replace-substring-renamer "SIMPLY" "STAR")
	   (replace-substring-renamer "READ" "WRITE")))

;; Apply the renamer to the symmetry.  This creates the constants
;; with%WRITE%access, etc, down to STAR%secure.   

(def-transported-symbols
  (with%read%access
   without%read%access 
   del%read%access get%read%access simply%secure)
  (translation access_records-symmetry)
  (renamer second-bl-renamer))

;; Make the images of all of our convergence theorems and rewrites available in
;; the names-changed, dual versions.   This will cause Imps to beep twice,
;; which you can safely ignore.   

(transport-convergence-and-rewrite-theorems (name->translation 'access_records-symmetry))

;; Nothing to prove in the next three theorems: We just reap the benefits
;; of symmetry.  A def-theorem form with a TRANSLATION slot will check that
;; the translation is in fact an interpretation.  Then it checks that the
;; mentioned theorem is really a theorem of the source theory.  Finally, it
;; applies the translation to get a new formula, which it installs into the
;; target theory.

(def-theorem get%write-preserves-star-security
  get%read-preserves-simple-security
  (theory access_records)
  (translation access_records-symmetry)
  (proof existing-theorem))

(def-theorem get%write-leaves-read-unchanged
  get%read-leaves-write-unchanged
  (theory access_records)
  (translation access_records-symmetry)
  (theory access_records)
  (proof existing-theorem))

(def-theorem star%security-depends-on-write
  simple%security-depends-on-read
  (translation access_records-symmetry)
  (macete beta-reduce)
  (theory access_records)
  (proof existing-theorem))

;; Now here's the explicit definition of when a state is secure.  

(def-constant secure%state
 "lambda(f:state, simply%secure(f) and star%secure(f))"
  (theory access_records))

;; Call the image of secure%state under the symmetry 'state%secure. 


(def-transported-symbols secure%state
  (translation access_records-symmetry)
  (renamer (lambda (a) 'state%secure)))

;; Prove that state%secure and secure%state mean just the same.  To prove
;; it, use extensionality, unfold-defined-constants and simplify; then type
;; capital D.

(def-theorem state%secure-reverse
  "state%secure=secure%state" 
  (theory access_records)
  (proof (extensionality
	  unfold-defined-constants
	  (prove-by-logic-and-simplification 3))))

(def-compound-macete state-secure-and-simplify
  (series (repeat state%secure-reverse)
	  simplify))

;; Here's the main security lemma, asserting that get%read preserves the
;; secure%state property.  To prove it:
;;
;; 1.  Unfold secure%state and simplify.
;; 2.  Apply macete get%read-preserves-simple-security.
;; 3.  Type capital D.
;; 4.  Instantiate the theorem star%security-depends-on-write for the before
;;     state s and the after state get%read%access(s,u,o).
;; 5.  Contrapose, so you can prove the negation of assumption 0.
;; 6.  Now use macete get%read-leaves-write-unchanged .

(def-theorem get%read-preserves-security
  "forall(s:state, u:user, o:object, 
	  secure%state(s)
	 implies
	  secure%state(get%read%access(s,u,o)))" 
  (theory access_records)
  (usages )
  (proof ((unfold-single-defined-constant-globally secure%state)
	  simplify
	  (apply-macete-with-minor-premises get%read-preserves-simple-security)
	  direct-and-antecedent-inference-strategy
	  (instantiate-theorem star%security-depends-on-write ("s" "get%read%access (s,u,o)"))
	  (contrapose "with(o:object,u:user,o_$0:object,u_$0:user,s:state,
  not(access_write(s(u_$0,o_$0))
      =access_write(get%read%access(s,u,o)(u_$0,o_$0))));")
	  (apply-macete-with-minor-premises get%read-leaves-write-unchanged)
	  simplify-insistently)))

;; The dual is free:  

(def-theorem get%write-preserves-security
   get%read-preserves-security
  (theory access_records)
  (translation access_records-symmetry)
  (macete state-secure-and-simplify)
  (usages )
  (proof existing-theorem))

;; And here is the corresponding lemma for del%read, with its dual.  The proof
;; is very similar to the proof of get%read-preserves-security.  

(def-theorem del%read-preserves-security
  "forall(s:state, u:user, o:object, 
	secure%state(s)
       implies
 	secure%state(del%read%access(s,u,o)))" 
  (theory access_records)
  (usages )
  (proof ((unfold-single-defined-constant-globally secure%state)
	  simplify
	  direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises del%read-preserves-simply%secure)
	  (instantiate-theorem star%security-depends-on-write ("s" "(del%read%access(s,u,o))"))
	  (contrapose "with(o:object,u:user,o_$0:object,u_$0:user,s:state,
  not(access_write(s(u_$0,o_$0))
      =access_write(del%read%access(s,u,o)(u_$0,o_$0))));")
	  (apply-macete-with-minor-premises del%read-leaves-write-unchanged)
	  simplify-insistently
	  )))

(def-theorem del%write-preserves-security
  del%read-preserves-security
  (theory access_records)
  (translation access_records-symmetry)
  (macete state-secure-and-simplify)
  (usages )
  (proof existing-theorem))

;; One final piddling fact about typings.  Not worth proving in the exercise
;; (though it's easy to prove).  Just evaluate.  

(def-theorem get%read-typing 
  "#(get%read%access,[state,user,object,state])"
  (theory access_records)
  (usages rewrite)
  (proof (sort-definedness-and-conditionals
	  simplify-insistently)))

;; At this point we can introduce a sort containing the commands to the state
;; machine that we will define in a minute.  These commands are just the four
;; functions we've been examining, namely get%read%access, get%write%access,
;; del%read%access and del%write%access.  

(def-atomic-sort command
  "lambda(f:[state,user,object,state], 
		f=get%read%access or f=get%write%access
	     or f=del%read%access or f=del%write%access )" 
  (theory access_records)
  (witness "get%read%access"))

;; Here's a macete to use what we know about all the possible command cases.  

(def-compound-macete command-security-cases
  (series
   simplify
   del%read-preserves-security
   del%write-preserves-security
   get%read-preserves-security
   get%write-preserves-security
   simplify))



(def-theorem command-cases 
  "forall(f:command, f=get%read%access or f=get%write%access
	        or f=del%read%access or f=del%write%access)"
  (theory access_records)
  (proof (direct-inference
	  (instantiate-theorem command-defining-axiom_access_records ("f"))
	  simplify)))

;;  Introduce arithmetic, which is needed for the state machine instantiation,
;;  because state machine histories are functions defined on (some) natural
;;  numbers.   

(def-theory access_records-1 
  (component-theories access_records h-o-real-arithmetic))

;; We now introduce one more record type.  The inputs to our state machine will
;; be records consisting of a command, a user, and an object.  The user and the
;; object are in effect the parameters to the command.  We call these input
;; records "actions". 

(define action_records
  (make-record-theory-with-sortnames
   (name->theory 'access_records-1)
   'action
   '((command "command")
     (user    "user")
     (object  "object"))))

(set (current-theory) action_records)

;; The transition function on our state machine takes an action, destructuring
;; it to apply the command to the two parameters.  

(def-constant next
 "lambda(f:state, a:action,
	action_command(a)(f,action_user(a),action_object(a)))"
  (theory action_records))

;; "Next" is a total function returning a state.  To prove this, unfold next
;; and simplify.  Then do a direct inference, and instantiate the theorem
;; "command-in-quasi-sort_access_records" where the instance of interest is
;; action_command(a).  Four top-most nodes will be left, corresponding to the
;; four cases.  Simplification proves each.

(def-theorem action_records-next-definedness
  "forall(a:action,s:state,#(next(s,a),state))"
  (theory action_records)
  (usages d-r-convergence)
  (proof ((unfold-single-defined-constant-globally next)
	  simplify
	  (instantiate-theorem
	   command-in-quasi-sort_access_records
	   ("action_command(a)"))
	  simplify-insistently
	  simplify-insistently
	  simplify-insistently
	  simplify-insistently)))

;; This theory interpretation formalizes the sense in which the action_records
;; theory describes a state machine.  The fact that we needed to define *both*
;; tr and next is an artifact of the way the deterministic state machine theory
;; is built up, starting from a sub-theory where the transition is a
;; non-deterministic relation, and later considering the deterministic case, in
;; which tr is the graph of a function next.   The presence of both s_init and
;; the initial predicate is similar.  

(def-theory-ensemble-instances
  det-state-machines-with-start
  (target-theories action_records)
  (sorts (state state) (action action))
  (multiples 1)
  (theory-interpretation-check using-simplification)
  (constants
   (tr "lambda(s:state, a:action, s_1:state, next(s,a)=s_1)")
   (next next)
   (initial "lambda(f:state, f=s_init)")
   (s_init s_init)
   (accepting "lambda(f:state, falsehood)")))

;; The next translation formalizes the fact that action_records is an instance
;; of the theory used for the fundamental security theorem.  It has one boring
;; obligation which can also be found in the file
;; $IMPS/theories/state-machines/bl-exercise-obligations.t

(def-translation fts->action_records
  force
  (source fts-theory)
  (target action_records)
  (core-translation det-state-machines-with-start-to-action_records)
  (constant-pairs
   (secure%state secure%state))
  (theory-interpretation-check using-simplification))

;; The next two theorems are interpretation obligations, but they are in fact
;; the main content of the assertion that our state machine is secure.  The
;; first asserts that the initial state is secure.  To prove it,
;; eliminate-definitions and simplify; then simplify insistently.

;; Use macete "eliminate-definitions-and-simplify", and then insistent
;; simplification (on both subgoals).  

(def-theorem fts+invariant->actions-ob1
  "secure%state(s_init);"
  (theory action_records)
  (proof ((apply-macete-with-minor-premises eliminate-definitions-and-simplify)
	  simplify-insistently
	  simplify-insistently)))

;; Unfold next; type capital D; then instantiate theorem
;; command-defining-axiom_access_records with instance action_command(a).  Four
;; subgoals (the four cases) will be left.  Use macete command-cases on each
;; one.
;;
;; NB:  This is almost the only case in which the macete you need DOES NOT
;; appear on the macete menu.  This is because it begins with a  "simplify." 

(def-theorem fts+invariant->actions-ob2
  "forall(s:state, 
    secure%state(s) 
   implies
    forall(a:action, 
     secure%state(next(s,a))));"
  (theory action_records)
  (proof ((unfold-single-defined-constant-globally next)
	  direct-and-antecedent-inference-strategy
	  (instantiate-theorem command-cases ("action_command(a)"))
	  (apply-macete-with-minor-premises command-security-cases)
	  (apply-macete-with-minor-premises command-security-cases)
	  (apply-macete-with-minor-premises command-security-cases)
	  (apply-macete-with-minor-premises command-security-cases)
	  )))

(def-translation fts+invariant->action_records
  (source fts+invariant)
  (target action_records)
  (core-translation fts->action_records)
  (theory-interpretation-check using-simplification))

;; Here is the assertion that the state machine is secure:  Every accessible
;; state is a secure%state.  To prove it, just get tr%fts+secure off the macete
;; menu.

(def-theorem bell_lapadula-security 
  "forall(s:state, accessible(s) implies secure%state(s))"
  (theory action_records)
  (proof ((apply-macete-with-minor-premises tr%fts+secure))))


