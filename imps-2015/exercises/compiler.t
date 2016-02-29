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

(herald exp-instr)

;; In this exercise, we prove the correctness of the world's smallest compiler.
;; It compiles programs in a "programming language" containing arithmetic
;; expressions with no variables.  The expressions are built up from numbers by
;; means of the operators plus and times.  
;; 
;; The "target code" consists of sequences of instructions for a stack machine.
;; The instructions consist of immediates (that are pushed onto the stack)
;; together with arithmetic operations that take their arguments off the stack,
;; combine them, and push the result.
;;
;; This example was suggested by Damir Jamsek (then of MCC).  The crucial lemma
;; was suggested by Matt Kauffman (Computational Logic, Inc).  

;; Following Imps's "Little Theories" approach, this file is introduces three
;; theories.  The first theory, EXP, specifies the source language.  It
;; illustrates how a BNF specification can be re-expressed as an axiomatic
;; theory (with an induction principle).  The BNF for EXP is:
;;
;;  EXP  ::= imm  x	    -- Injection of a real x into EXP 
;;  EXP  ::= (e_0 + e_1)    -- Exp of two EXPs is a EXP
;;  EXP  ::= (e_0 * e_1)    -- Product of two EXPs is a EXP
;;
;; The specification also introduces "value" as a selector ("destructor") for
;; immediates, as well as {first,second}%{addend,factor} as the four selectors
;; for plus and times expressions.

(load-section sequences)

;; (!)

(def-bnf exp
  (theory h-o-real-arithmetic)
  (base-types exp)
  (constructors
   (imm (rr exp)
	(selectors value))
   (plus (exp exp exp)
	 (selectors first%addend second%addend))
   (times (exp exp exp)
	  (selectors first%factor second%factor))))

;; Make this theory be the default for reading expressions and for starting
;; proofs: 

(set (current-theory) (name->theory 'exp))

;; (!)
;; Our next job is to define the "DENOTATIONAL SEMANTICS" of our programming
;; language EXP.  In our case, the semantics is given by a simple recursively
;; defined function from EXPs to numbers.  The resulting number is the
;; denotation of the program.   

;; Formally, the function is introduced by primitive recursion on the structure
;; of values belonging to the BNF-style data type.  

;; The second argument, "exp" in this case, indicates which BNF the recursion
;; is over.  The keyword "theory" indicates which theory the resulting
;; expression is intended for.  This may be a super-theory of the one that the
;; BNF introduces.  The "compile" function at the bottom of this file is an
;; example where the target theory is a strict super-theory.  

;; The sort of the function being introduced is bnf-base-type --> range-sort,
;; or in the case at hand, exp --> rr.  Primitive recursions with parameters
;; may be introduced in curried form, with range-sort itself a function sort.
;; The functions ev_one, ev_stream and append%stream introduced below are
;; examples.

;; The remainder of the form consists of the clauses for the individual cases,
;; keyed by atom or constructor (in this case there are only constructors).
;; The variable names in parentheses are associated with the successive
;; arguments to the constructors.  The expression read from the string is
;; interpreted as a function of these variables.  The sorts of the variables is
;; determined as follows:
;;
;; 1.  If that position in the constructor does not belong to the base-type,
;;     then the variable is of the same sort as the argument.  For instance,
;;     imm:[rr,exp] takes a real number, so the x in the clause for imm is of
;;     sort rr.
;; 2.  If that position in the constructor does belong to the base-type, then
;;     the primitive recursion schema has a recursive call in that position.
;;     The variable represents the *result* of the recursive call, and is
;;     therefore of the range sort.  For instance, plus:[exp, exp, exp] takes
;;     two EXPs, so the x and y in the clause for plus are of the range sort,
;;     namely rr.  When we're computing ev_e(plus(e_0,e_1)), x and y represent the
;;     values ev_e(e_0) and ev_e(e_1).  Thus the clause states that
;;
;;       ev_e(plus(e_0,e_1))=ev_e(e_0)+ev_e(e_1).
;;
;;     The constructor times is similar.
;; 

(def-primitive-recursive-constant ev_e
  exp
  (theory exp)
  (range-sort rr)
  (imm (x) "x")
  (plus (x y) "x+y")
  (times (x y) "x*y"))

;; (!)
;; This is in fact a total function.  Prove:
;;   "total_q{ev_e, [exp,rr]}"
;;
;;   To carry out the proof, use induction (on the command menu).  In the
;;   induction step, use unfold-defined-constants and simplify for each
;;   subgoal.    

(def-theorem ev_e-totality
  "total_q{ev_e, [exp,rr]}"
  (theory exp)
  (usages d-r-convergence)
  (proof (
	  (induction exp-exp-inductor ("x_0"))	  
	  )))

;; (!)
;; This completes our development of the theory of EXP on its own.  We turn
;; next to the machine code, embodied in a theory INSTR about instructions on
;; our target stack machine.  This is also presented as a BNF, but there are no
;; recursive cases in the specification.  Thus instructions are essentially a
;; union type of the atoms add and mult, together with one place records
;; imm_i(x:rr) with one real field.  

(def-bnf instructions
  (theory h-o-real-arithmetic)
  (base-types instr)
  (atoms (add instr)
	 (mult instr))
  (constructors
   (imm_i (rr instr))))

;; (!)
;; For variety here, we introduce instruction_streams not as finite sequences
;; of instructions (in the sense of certain partial functions from natural
;; numbers to instructions), but rather as "abstract lists" of instructions.
;; The abstract lists are constructed using:
;;  1.  "term" to construct a terminated (singleton) list containing only the
;;  	single instruction given as its argument, and
;;  2.  "prepend" to construct a list of length n+1 given an instruction and an
;;  	instruction list of length n.
;;  Selectors are "last" to take the only instruction in a terminated list, and
;;  "first" and "rest" to take the head instruction and remaining list of a
;;  prepended instruction stream.   


(def-bnf instruction_streams
  (theory instructions)
  (base-types instr_stream)
  (constructors
   (term "[instr, instr_stream]" (selectors last))
   (prepend "[instr, instr_stream, instr_stream]" (selectors first rest))))

;; Make this theory be the default for reading expressions and for starting
;; proofs: 

(set (current-theory) (name->theory 'instruction_streams))

;; (!)
;; Now we define the "OPERATIONAL SEMANTICS" of a single instruction,
;; executing on an initial stack.  It returns another stack:
;; 1.  An immediate pushes the value.
;; 2.  Add and mult pop the top two values off the stack and push their sum or
;;     product respectively.  

;; Formally, ev_one is a curried function defined by primitive recursion.  It
;; takes as argument an i:instr, and returns a function of sort
;; "[[nn,rr],[nn,rr]]".  That is, the resulting fn, when applied to a
;; stack:[nn,rr], returns another stack of the same sort.  The notation for
;; primitive recursive is a bit tricky, even though this example is not
;; "really" recursive, but essentially a definition by cases (see the next
;; example for a more demanding definition).  

;; Here, the quoted string indicates the return value, which as expected is a
;; function which takes as argument a stack s:[nn,rr] and returns a value of
;; the same sort.  In the case of imm_i, the value depends on an argument to
;; the data type constructor ranging over the reals.  Because the argument
;; ranges over the reals rather than (recursively) over instructions, x ranges
;; over rr, as described above.

(def-primitive-recursive-constant ev_one
  instructions
  (theory instructions)
  (range-sort "[[nn,rr],[nn,rr]]")
  (add  "lambda(s:[nn,rr], cons{s(0)+s(1),drop{s,2}})")
  (mult "lambda(s:[nn,rr], cons{s(0)*s(1),drop{s,2}})")
  (imm_i (x) "lambda(s:[nn,rr], cons{x,s})"))

;; (!)
;; Now we define the "OPERATIONAL SEMANTICS" of a sequence of instructions,
;; executing on an initial stack.  A null instruction sequence returns its
;; stack as the final result.  Add and mult push the result of applying the
;; operation to the top two stack elements.  An immediate simply gets pushed
;; onto the stack.   

;; In this case, the recursion is a genuine one.  Consider the data type
;; constructor "prepend", which takes i:instr and code:instr_stream as its
;; arguments.  Since i does not belong to the type of instruction streams, the
;; recursion must terminate with it.  On the other hand, since the argument
;; code does belong to the type, we must recursively apply ev_stream to it.
;; The Imps primitive recursive definition mechanism takes care of applying the
;; new constant to arguments in the type of the recursion.  Hence, the user may
;; introduce the variable rest_val, taken to be of sort [[nn,rr],[nn,rr]].  It
;; represents the result of applying ev_stream recursively to the argument code
;; (representing the rest-code of the prepend).   

;; This typechecks properly: (ev_one(i)(s)) is a stack of sort [nn,rr], so that
;; rest_val(ev_one(i)(s)) is another stack of sort [nn,rr], and
;; lambda(s:[nn,rr], rest_val(ev_one(i)(s))) is a function of sort
;; [[nn,rr],[nn,rr]], which is the expected range sort of the definition.

(def-primitive-recursive-constant ev_stream
  instruction_streams
  (theory instruction_streams)
  (range-sort "[[nn,rr],[nn,rr]]")
  (term (i) "ev_one(i)")
  (prepend (i rest_val) "lambda(s:[nn,rr], rest_val(ev_one(i)(s)))"))

;; The following script raises the 0th conditional term 
;; -- i.e. it rewrites phi(if(psi,s,t)) as if_form(psi, phi(s), phi(t)) --
;; until there are no more conditional terms.  It is recognized as applicable
;; (and thus put on the command menu) when the sequent node assertion satisfies
;; the recognizer for raise-conditional.  

(def-script raise-all-conditionals 0

  ((while (progresses? (raise-conditional (0))) (skip)))

  (applicability-recognizer
   (lambda (sqn) (rc-i-applicable? (sequent-node-assertion sqn)))))

;; The value of ev_one is always a total function.  The proof requires us to
;; take cases on the sort instr in the BNF instructions.  

(def-theorem ev_one-definedness-lemma 
  "forall(i:instr,forall(s:[nn,rr],#(ev_one(i)(s))))"
  (usages rewrite)
  (theory instructions)
  (proof (
	  (unfold-single-defined-constant-globally ev_one)
	  insistent-direct-and-antecedent-inference-strategy
	  raise-all-conditionals
	  (label-node before-cases)
	  (bnf-take-cases instr-cases_instructions ("i"))
	  (jump-to-node before-cases)
	  (for-nodes
	   (unsupported-descendents)
	   simplify)
	  )))

;; Similarly, the value of ev_stream is always a total function.  The proof is
;; by induction on the data type, although the induction machinery requires us
;; to break up the simultaneously bound variables in the statement of the
;; theorem.  In particular, we need the "stronger" induction predicate which
;; asserts that for all stacks the value is defined.  

(def-theorem ev_stream-definedness
  "forall(code:instr_stream, stack:[nn,rr], #(ev_stream(code)(stack)))"
  (usages rewrite)
  (proof
   (
    (cut-with-single-formula
     "forall(code:instr_stream, forall(stack:[nn,rr], #(ev_stream(code)(stack))))")
    simplify
    (induction instr_stream-instruction_streams-inductor ("code"))
    (jump-to-node induction-step)
    (for-nodes
     (unsupported-descendents)
     (block 
       insistent-direct-and-antecedent-inference-strategy
       simplify-insistently))))
  (theory instruction_streams))

;; Of course an immediate consequence of #(ev_stream(code)(stack)) is the
;; definedness of the intermediate result, i.e.  #(ev_stream(code)).  Stating
;; this as a separate theorem smooths other proofs below.

(def-theorem ev_stream-definedness-weak
  "forall(code:instr_stream, #(ev_stream(code)))"
  (usages rewrite)
  (proof
   (	  
    (assume-theorem ev_stream-definedness)
    simplify-insistently))
  (theory instruction_streams))

;; (!)
;; Because we chose in this example to represent the instruction streams by
;; abstract lists, we define an append operator on them by primitive recursion
;; on the first argument.  append%streams is curried, and append%streams(c_0)
;; is a function which if applied to c_1 returns the appended instr_stream.

;; The implicit sort of rest_val in the "prepend" clause is the range-sort
;; [instr_stream,instr_stream].  It represents the result of the recursive
;; call, so that
;;
;; 	append%streams(prepend(i,s))(c)=prepend(i,append%streams(s)(c))
;; 

(def-primitive-recursive-constant append%streams
  instruction_streams
  (theory instruction_streams)
  (range-sort "[instr_stream,instr_stream]")
  (term (i) "lambda(c:instr_stream, prepend(i,c))")
  (prepend (i rest_val) "lambda(c:instr_stream, prepend(i, rest_val(c)))"))

(comment
 ;;
 ;; example:
 ;; To prove this equation, unfold and simplify
 ;; 
 "with(c,y:instr_stream, i_0,i_1:instr,
    append%streams(prepend(i_0, term(i_1)))(c)
   = prepend(i_0,prepend(i_1,c)))")

;; append%streams is of course also a total function.  

(def-theorem append%streams-definedness
  "forall(c_0:instr_stream,
      forall(c_1:instr_stream, #(append%streams(c_0)(c_1))))"
  (usages rewrite)
  (proof
   (
    (induction instr_stream-instruction_streams-inductor ("c_0"))    
    (jump-to-node induction-step)
    (for-nodes (unsupported-descendents) simplify-insistently)))
  (theory instruction_streams))

;; (!)
;; This is the main lemma that justifies the compilation approach.  It states
;; that the result of executing an appended instruction stream on an initial
;; stack is the same as the result of executing the second instruction stream
;; on the stack resulting from executing the first stream on the initial stack.
;;
;; The cognoscenti refer to this as "Matt's lemma".
;;
;; Proof uses induction and then a backchain.  

(def-theorem ev_stream-append
  "forall(c_0:instr_stream,
      forall(c_1:instr_stream,s:[nn,rr],
      ev_stream(append%streams(c_0)(c_1))(s)=ev_stream(c_1)(ev_stream(c_0)(s))))"
  (proof
   (
    
    (induction instr_stream-instruction_streams-inductor ())
    (backchain "with(y%prepend_1:instr_stream,
  forall(c_1:instr_stream,s:[nn,rr],
    ev_stream(append%streams(y%prepend_1)(c_1))(s)
    =ev_stream(c_1)(ev_stream(y%prepend_1)(s))));")
    ))
  (theory instruction_streams))


;; (!)
;; Up to now, we have defined the source language and the target architecture.
;; We will now combine the two theories, and define the COMPILE function as a
;; function from EXP to code sequences (themselves functions from NN to INSTR).

(def-theory compiler
  (component-theories exp instruction_streams))

;; Make this theory be the default for reading expressions and for starting
;; proofs: 

(set (current-theory) (name->theory 'compiler))

;; (!)
;; Here is the compiler.  It is defined by primitive recursion.  Note that in
;; the clauses for plus and times, the arguments str_0 and str_1 refer to the
;; result of applying compile recursively to the sub-expressions.  This is in
;; line with the convention, described above, that when the argument to a
;; constructor is of the domain sort, it will be subjected to a recursive call.
;; 

(def-primitive-recursive-constant compile
  exp
  (theory compiler)
  (range-sort instr_stream)
  (imm (x) "term(imm_i(x))")
  (plus (str_0 str_1) "append%streams(str_0)(append%streams(str_1)(term(add)))")
  (times (str_0 str_1) "append%streams(str_0)(append%streams(str_1)(term(mult)))"))


;; (!)
;; COMPILE is in fact a total function.  This is really a part of the
;; correctness theorem, as a partial function would not satisfy a programmer,
;; who would not want the compiler to be undefined for his program.
;; 
;; Just use induction.
;;

(def-theorem compile-total
  "forall(e:exp, #(compile(e)))"
  (theory compiler)
  (proof
   (
    (induction exp-exp-inductor ("e"))))
  (usages d-r-convergence))


;; (!)

;; We are now ready for the main theorem, that the "operational semantics" of
;; COMPILE's output matches the "denotational semantics" of the source program.
;; The sense of "match" relevant here is that we can run the target code
;; starting with any stack on the target machine, and the eventual result is to
;; push the denotation of the source program onto the stack.
;;
;;    "forall(e:exp, forall(s:[nn,rr], ev_stream(compile(e))(s) = cons{ev_e(e),s}))"
;;
;; To prove the theorem, take the following steps:
;;  1.  Use induction.
;;  2.  In the induction step, use the macete constructed above,
;;	ev_r-append repeatedly.
;;  3.  Backchain-repeatedly against both assumptions.
;;  4.  The resulting expression involves occurrences of
;;      drop{cons{..., cons{..., ...}}, 2}.  The macete
;;      drop-cons-and-simplify will repeatedly appy the relevant
;;      conditional rewrite and then simplify.  
;; 


(def-theorem compiler-correctness
  "forall(e:exp, forall(s:[nn,rr], ev_stream(compile(e))(s) = cons{ev_e(e),s}))"
  (theory compiler)
  (proof (
	  (induction exp-exp-inductor ("e"))
	  (jump-to-node induction-step)
	  (let-macete
	   ev_s-append-repeatedly
	   (sequential (repeat ev_stream-append) simplify))
	  (for-nodes
	   (unsupported-descendents)
	   (block 
	     (apply-macete-with-minor-premises $ev_s-append-repeatedly)
	     (backchain-repeatedly (* "with(y%plus_1:exp,
  forall(s:[nn,rr],
    ev_stream(compile(y%plus_1))(s)=cons{ev_e(y%plus_1),s}))"))
	     simplify
	     (apply-macete-with-minor-premises drop-cons-and-simplify))))))

	   

;; The current mechanism for defining a function by primitive recursion over a
;; BNF data type is fairly good.  However, one possible gap in the BNF
;; machinery has to do with the totality of functions defined by primitive
;; recursion.  In order to prove that the resulting function is total (if it
;; is), the user must provide a direct proof.  In fact, it's always enough to
;; prove that the functional arguments to the PR schema are total.  In any case
;; where the totality of a particular primitive recursively defined expression
;; is hard to prove directly, it would be easy to prove the general fact about
;; the schema just mentioned, and to apply it to the functional arguments in
;; the particular PR definition at hand.  See
;;     ~guttman/imps/theories/pr-totality.t
;; for a six-step proof of the general fact for the EXP PR schema.
