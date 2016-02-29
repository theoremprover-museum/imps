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

(herald flatten)

(load "~guttman/imps/theories/user-commands.t")
(load-section sequences)

(def-language non-control-language 
  (base-types instr state answer)
  (constants
   (truthful "[state, prop]")
   (next "[state, instr, state]")
   (val_final "[state, answer]")))


(def-theory non-control-instructions
  (component-theories h-o-real-arithmetic)
  (language non-control-language)
  (axioms
   (next-total "forall(s:state, i:instr, #(next(s,i)))" d-r-convergence)
   (val_final-total "forall(s:state, #(val_final(s)))" d-r-convergence)))


(def-bnf code 
  (theory non-control-instructions)
  (base-types code)
  (atoms (null%code code))
  (constructors
   (prepend "[instr, code, code ]" (selectors first rest))
   (unless%false "[code, code, code, code ]"
		 (selectors consequent alternative after%code))))

(def-primitive-recursive-constant run_code
  code
  (theory code)
  (range-sort "[state,state]")
  (null%code "lambda(s:state, s)")
  (prepend
   (i rest_val)
   "lambda(s:state, rest_val(next(s,i)))")
  (unless%false
   (conseq_val alt_val after_val)
   "lambda(s:state, 
       if(truthful(s),
	  after_val(conseq_val(s)),
	  after_val(alt_val(s))))"))


(def-theorem run_code-totality
  "forall(c:code, s:state, #(run_code(c)(s)))"
  (theory code)
  (usages rewrite)
  (proof
   (
    (cut-with-single-formula "forall(c:code,forall(s:state,#(run_code(c)(s))))")
    simplify
    (induction code-code-inductor ("c"))
    simplify-insistently
    (jump-to-node induction-step)
    (for-nodes
     (unsupported-descendents)
     (block simplify-insistently (raise-conditional (0)) simplify)))))

(def-theorem run_code-totality-weak
  "forall(c:code, #(run_code(c)))"
  (theory code)
  (usages rewrite d-r-covergence)
  (proof
   (
    (assume-theorem run_code-totality)
    simplify-insistently)))

(def-constant ev_code "lambda(c:code, lambda(s:state, val_final(run_code(c)(s))))"
  (theory code))

(def-bnf flattened-instructions
  (theory non-control-instructions)
  (base-types instr_f)
  (constructors
   (nc "[instr, instr_f]" (selectors nc_instr))
   (jump "[nn, instr_f]" (selectors jump_length))
   (jump%false "[nn, instr_f]" (selectors jumpf_length))))

(def-theory flattener (component-theories code flattened-instructions))

(def-primitive-recursive-constant flatten
  code
  (theory flattener)
  (range-sort "[nn,instr_f]")
  (null%code "nil{instr_f}")
  (prepend (i rest_val) "cons{nc(i),rest_val}")
  (unless%false
   (conseq_seq alt_seq after_seq)
   "append{cons{jump%false(length{conseq_seq}+1),conseq_seq},
     append{cons{jump(length{alt_seq}),alt_seq}, 
      after_seq}}"))
	   
;; Simplify this:
"with(i,j, k:instr, s:[nn,instr_f],
   s=flatten(
       unless%false(
	prepend(i, null%code), 
	prepend(j, null%code), 
	prepend(k, null%code))))"

;; to get
;;
"with(k,j,i:instr,s:[nn,instr_f],
  s=seq{jump%false(2),nc(i),jump(1),nc(j),nc(k),instr_f});"

(def-theorem flatten_totality
  "forall(c:code, #(flatten(c)))"
  (theory flattener)
  (usages d-r-convergence)
  (proof ((induction code-code-inductor ("c")))))

(def-theorem flatten-is-f_seq
  "forall(c:code, f_seq_q{flatten(c)})"
  (theory flattener)
  (usages rewrite)
  (proof ((induction code-code-inductor ("c")))))


(def-recursive-constant run_flat
  "lambda(rf:[[nn,instr_f],state,state],
     lambda(f:[nn,instr_f],s:state,
       if(f=nil{instr_f}, 
	    s, 
	  #(    nc_instr(f(0))), 
	    rf(drop{f,1},next(s,nc_instr(f(0)))), 
	  #(jumpf_length(f(0))) and truthful(s), 
	    rf(drop{f,1},s), 
	  #(jumpf_length(f(0))) and not(truthful(s)), 
	    rf(drop{f,jumpf_length(f(0))+1},s), 
	  #( jump_length(f(0))), 
	    rf(drop{f,jump_length(f(0))+1},s),
	    ?state)))"
  (theory flattener))




(def-script run_flat-cases-prover 0
  ((unfold-single-defined-constant (0) run_flat)
   simplify
   (apply-macete-with-minor-premises drop-cons-and-simplify)))

(def-theorem run_flat-nil
  "forall(s:state, run_flat(nil{instr_f},s)=s)"
  (theory flattener)
  (usages rewrite)
  (proof (run_flat-cases-prover)))

(def-theorem run_flat-non-control
  "forall(f:[nn,instr_f], s:state, i:instr, 
    run_flat(cons{nc(i),f},s)==run_flat(f,next(s,i)))"
  (theory flattener)
  (usages rewrite)
  (proof (run_flat-cases-prover)))

(def-theorem run_flat-jump%false
  "forall(f:[nn,instr_f], s:state, n:nn, 
    run_flat(cons{jump%false(n),f},s)
  ==if((truthful(s)),run_flat(f,s), run_flat(drop{f,n},s)))"
  (theory flattener)
  (usages rewrite)
  (proof (run_flat-cases-prover)))

(def-theorem run_flat-jump
  "forall(f:[nn,instr_f], s:state, n:nn, 
    run_flat(cons{jump(n),f},s)
  ==run_flat(drop{f,n},s))"
  (theory flattener)
  (usages rewrite)
  (proof (run_flat-cases-prover)))

(def-compound-macete run_flat-cases
  (repeat run_flat-nil run_flat-non-control run_flat-jump%false run_flat-jump))

(def-script raise-all-conditionals 0

  ((while (progresses? (raise-conditional (0))) (skip)))

  (applicability-recognizer
   (lambda (sqn)
     (rc-i-applicable? (sequent-node-assertion sqn)))))

(def-translation sequences->flattener
  (source sequences)
  (target flattener)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 instr_f))
  (theory-interpretation-check using-simplification))

(def-inductor flattener_seq-inductor 
  sequence-induction
  (theory flattener)
  (translation sequences->flattener)
  (base-case-hook simplify))


;; This proof is a bit long, and finding the right initial cut formula took
;; some practice.

(def-theorem run_flat-defined-for-f_seq
  "forall(f:[nn,instr_f],s:state, f_seq_q{f} implies #(run_flat(f,s)))"
  (theory flattener)
  (proof
   (
    (cut-with-single-formula "forall(f:[nn,instr_f], 
	f_seq_q{f}
       implies
        forall(j:nn,s:state, #(run_flat(drop{f,j},s))))")
    (block
      (script-comment "we will first show that the cut formula entails the theorem.")
      direct-and-antecedent-inference-strategy
      (auto-instantiate-universal-antecedent "forall(f:[nn,instr_f],
  f_seq_q{f}
   implies 
  forall(j:nn,s:state,#(run_flat(drop{f,j},s))));")
      (instantiate-universal-antecedent "with(p:prop,forall(j:nn,s:state,p));"
					("0" "s"))
      (simplify-antecedent "with(s:state,#(s));"))
    (induction flattener_seq-inductor ("f"))
    (case-split ("j=0"))
    (move-to-sibling 2)
    (block
      (script-comment "first we take the 'boring' case j>0")
      (instantiate-universal-antecedent "with(p:prop,forall(j:nn,s:state,p));"
					("j-1" "s"))
      (incorporate-antecedent "with(s:state,#(s));")
      (apply-macete-with-minor-premises drop-cons-and-simplify))
    (block
      (script-comment "we will simplify to use the fact that j=0, and then introduce a script to do the remainder of the work.")
      simplify
      (let-script
       do-case 1
       ((backchain-backwards "with(e,i:instr_f,i=e);")
	(apply-macete-with-minor-premises run_flat-cases)
	(if (matches? "with(p:prop,s:state, #(if(p,s,s)));")
	    (case-split-on-conditionals (0))
	    (skip))
	(instantiate-universal-antecedent "with(s_$0:[nn,instr_f],
  forall(j:nn,s:state,#(run_flat(drop{s_$0,j},s))));"
					  ("0" $1))
	(simplify-antecedent "with(f:[nn,instr_f],s:state,
  #(run_flat(f,s)));")))
      (instantiate-theorem instr_f-cases_flattened-instructions ("e"))
      ($do-case "next(s,nc_instr(e))")
      ($do-case "s")
      ($do-case "s")))))


(def-theorem run_flatten-defined-for-flatten-output
  "forall(c:code, s:state, #(run_flat(flatten(c),s)))"
  (theory flattener)
  (usages rewrite)
  (proof (
	  (apply-macete-with-minor-premises run_flat-defined-for-f_seq)
	  (apply-macete-with-minor-premises flatten-is-f_seq))))


(def-constant regular%instr_f
  "lambda(f:[nn,instr_f], f_seq_q{f} and 
    forall(n,o:nn, (f(n)=jump(o) or f(n)=jump%false(o))
      implies n+o<length{f}))"
  (theory flattener))

(def-theorem regular-is-f_seq
  "forall(f:[nn,instr_f], regular%instr_f(f) implies f_seq_q{f})"
  (theory flattener)
  (proof (
	  (unfold-single-defined-constant-globally regular%instr_f)
	  simplify)))

(def-script regular-jump?_length 3
  ;;
  ;; arguments are constructor and selector names, and definedness theorem
  ;; 
  ((unfold-single-defined-constant-globally regular%instr_f)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,forall(n,o:nn,p));"
				      ("n" (% "(~a(f(n)))" $2)))
    (contrapose (% "with(n:nn,f:[nn,instr_f],not(f(n)=~a(n)));" $1))
    (instantiate-theorem $3 ("f(n)"))
    (force-substitution "(f(n))" (% "~a(y_0)" $1) (1))
    simplify))
  

(def-theorem regular-jumpf_length
  "forall(f:[nn,instr_f],n:nn,
    regular%instr_f(f) and #(jumpf_length(f(n))) 
   implies
    n+jumpf_length (f(n))<length{f})"
  (theory flattener)
  (proof
   (
    (regular-jump?_length
     "jump%false" "jumpf_length"
     jumpf_length-definedness_flattened-instructions))))

(def-theorem regular-jump_length
  "forall(f:[nn,instr_f],n:nn,
    regular%instr_f(f) and #(jump_length(f(n))) 
   implies
    n+jump_length (f(n))<length{f})"
  (theory flattener)
  (proof
   (
    (regular-jump?_length
     "jump" "jump_length"
     jump_length-definedness_flattened-instructions))))

(def-theorem regular-jump_length-macete
  "forall(f:[nn,instr_f],o,n,k:nn,
    f(n)=jump(o) and regular%instr_f(f) and length{f}<=k
   implies
    n+o<k)"
  (theory flattener)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem regular-jump_length ("f" "n"))
    (contrapose "with(p:prop,not(p));")
    simplify
    (incorporate-antecedent "with(f:[nn,instr_f],n:nn,n+n<length{f});")
    simplify)))

(def-theorem regular-jumpf_length-macete
  "forall(f:[nn,instr_f],o,n,k:nn,
    f(n)=jump%false(o) and regular%instr_f(f) and length{f}<=k
   implies
    n+o<k)"
  (theory flattener)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem regular-jumpf_length ("f" "n"))
    (contrapose "with(p:prop,not(p));")
    simplify
    (incorporate-antecedent "with(f:[nn,instr_f],n:nn,n+n<length{f});")
    simplify)))

(def-theorem regular-preserved-by-drop
  "forall(f_0,f_1:[nn,instr_f], n:nn, regular%instr_f(f_0)
  implies regular%instr_f(drop{f_0,n}))"
  (theory flattener)
  (proof
   (
    (unfold-single-defined-constant-globally regular%instr_f)
    (apply-macete-with-minor-premises tr%drop-is-fseq)
    direct-inference-strategy
    (move-to-ancestor 1)
    (apply-macete-with-minor-premises tr%length-of-drop)
    simplify
    (antecedent-inference "with(p:prop,p and p);")
    (instantiate-universal-antecedent "with(p:prop,forall(n,o:nn,p));"
				      ("n+n_$0" "o_$0"))
    simplify
    (case-split-on-conditionals (0)))))

(def-theorem regular-preserved-by-append
  "forall(f_0,f_1:[nn,instr_f], regular%instr_f(f_0) and regular%instr_f(f_1)
  implies regular%instr_f(append{f_0,f_1}))"
  (theory flattener)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "f_seq_q{f_0} and f_seq_q{f_1}")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises regular-is-f_seq)
    simplify
    (incorporate-antecedent "with(f_0:[nn,instr_f],regular%instr_f(f_0));")
    (incorporate-antecedent "with(f_1:[nn,instr_f],regular%instr_f(f_1));")
    (unfold-single-defined-constant-globally regular%instr_f)
    (apply-macete-with-minor-premises tr%length-of-append)
    (apply-macete-with-minor-premises tr%append-is-fseq)
    direct-inference
    direct-inference
    direct-inference
    direct-inference
    (case-split-on-conditionals (0))
    (let-script
     do-case 2
     ;; arguments are variable name "f_0" or "f_1" naming the subsequence at issue,
     ;; and the index into it.
     ((antecedent-inference
       (% "with( ~A :[nn,instr_f],
  f_seq_q{ ~A }
   and 
  forall(n,o:nn,
    ( ~A (n)=jump(o) or  ~A (n)=jump%false(o))
     implies 
    n+o<length{ ~A }));"
	  $1 $1 $1 $1 $1))
       (instantiate-universal-antecedent "with(p:prop,forall(n,o:nn,p));"
				      ($2 "o_$0"))
       simplify
       simplify))
    ($do-case "f_1" "n_$0+[-1]*length{f_0}")
    ($do-case "f_0" "n_$0"))))


(def-theorem regular-preserved-by-cons-nc-i
  "forall(f:[nn,instr_f], i:instr, regular%instr_f(f) 
  implies regular%instr_f(cons{nc(i),f}))"
  (theory flattener)
  (proof 
   (
    (unfold-single-defined-constant-globally regular%instr_f)
    simplify
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 3)
    (case-split-on-conditionals (0))
    (antecedent-inference "with(p:prop,p and p);")
    (instantiate-universal-antecedent "with(p:prop,forall(n,o:nn,p));"
				      ("[-1]+n_$0" "o_$0"))
    simplify
    simplify)))

(def-theorem regular-preserved-by-jump%false
  "forall(f_0,f_1:[nn,instr_f], 
     regular%instr_f(f_0) and regular%instr_f(f_1) and not(f_1=nil{instr_f})
    implies 
     regular%instr_f(
      append{cons{jump%false(1+length{f_0}), f_0},f_1}))"
  (theory flattener)
  (proof
   (
    (let-script
     do-subcase 1
     ((if (matches?
	   "with(p:prop, f:[nn,instr_f],j:nn,x:rr,i:instr_f, f(([-1]+j)+x)=i implies p)")
	  (force-substitution "n_$0+o_$0<1+length{f_0}+length{f_1}"
			      "([-1]+n_$0+[-1]*length{f_0})+o_$0<length {f_1}"
			      (0))
	  (force-substitution "n_$0+o_$0<1+length{f_0}+length{f_1}"
			      "([-1]+n_$0)+o_$0<length{f_0}+length{f_1}"
			      (0)))
      justify-forced-substitution
      (apply-macete-with-minor-premises $1)
      direct-inference
      auto-instantiate-existential
      simplify))

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "f_seq_q{f_0} and f_seq_q {f_1} and not(length {f_1}=0)")
    (script-comment "immediately establish finiteness and that f_1 is long enough.")
    (move-to-sibling 1)
    (let-macete
     regularity-and-length
     (series (repeat regular-is-f_seq tr%length-0-iff-nil) simplify))
    (apply-macete-with-minor-premises $regularity-and-length)
    (unfold-single-defined-constant-globally regular%instr_f)
    (let-macete
     fseq-and-length
     (repeat tr%append-is-fseq tr%cons-is-fseq tr%length-of-cons tr%length-of-append))
    (apply-macete-with-minor-premises $fseq-and-length)
    direct-and-antecedent-inference-strategy
    (block (script-comment "case for jump instruction.")
	   (incorporate-antecedent "with(i:instr_f,i=i);")
	   (case-split-on-conditionals (0))
	   (block (script-comment "subcase: jump occurs in f_1.")
		  ($do-subcase regular-jump_length-macete))
	   (case-split-on-conditionals (0))
	   (block (script-comment "subcase: jump occurs in f_0.")
		  ($do-subcase regular-jump_length-macete)))
    (block (script-comment "case where instruction is jump%false")
       (incorporate-antecedent "with(i:instr_f,i=i);")
       (case-split-on-conditionals (0))
       (block (script-comment "subcase jump%false occurs in f_1.")
              ($do-subcase regular-jumpf_length-macete))
       (case-split-on-conditionals (0))
       simplify
       (block (script-comment "subcase: 1+length{f_0}=o_$0. Use injectiveness")
              (force-substitution "o_$0" "(1+length{f_0})" (1))
              simplify
              (instantiate-theorem jump%false-injectiveness_flattened-instructions
                                   ("(1+length{f_0})" "o_$0")))
       (block (script-comment "subcase jump%false occurs in f_0.")
              ($do-subcase regular-jumpf_length-macete))))))

(def-theorem regular-preserved-by-jump
  "forall(f_0:[nn,instr_f], 
     regular%instr_f(f_0)
    implies 
     regular%instr_f(
      cons{jump(length{f_0}),
                    f_0}))"
  (theory flattener)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "f_seq_q{f_0}")
    (block (script-comment "immediately establish finiteness.")
	   (move-to-sibling 1)
	   (apply-macete-with-minor-premises regular-is-f_seq))
    (unfold-single-defined-constant-globally regular%instr_f)
    simplify
    (raise-conditional (0 1))
    direct-and-antecedent-inference-strategy
    (block
      (script-comment "Case of new jump instruction.")
      (instantiate-theorem jump-injectiveness_flattened-instructions
			   ("(length{f_0})" "(o_$0)"))
      simplify)
    (let-script
     use-regularity 1
     ((force-substitution "n_$0+o_$0<1+length{f_0}"
			  "([-1]+n_$0)+o_$0<length{f_0}"
			  (0))
      justify-forced-substitution
      (apply-macete-with-minor-premises $1)
      auto-instantiate-existential
      simplify))
    (block (script-comment "Case of jump in old code.")
	   ($use-regularity regular-jump_length-macete))
    (block (script-comment "Bogus case in which  jump(n)=jump%false(m).")
	   (contrapose "with(i:instr_f,i=i);")
	   simplify)
    (block (script-comment "Case of jump%false in old code.")
	   ($use-regularity regular-jumpf_length-macete))
    )))


(def-theorem null-flattened-code-is-regular
  "regular%instr_f(nil{instr_f})"
  (theory flattener)
  (usages rewrite)
  (proof
   (
    (unfold-single-defined-constant-globally regular%instr_f)
    simplify)))


(def-theorem flatten-is-regular
  "forall(c:code, regular%instr_f(flatten(c)))"
  (theory flattener)
  (usages rewrite)
  (proof
   (
    (induction code-code-inductor ("c"))
    (apply-macete-with-minor-premises regular-preserved-by-cons-nc-i)
    (let-macete cons-append-repeatedly (repeat tr%cons-append))
    (apply-macete-with-minor-premises $cons-append-repeatedly)
    (apply-macete-with-minor-premises tr%cons-append)
    (apply-macete-with-minor-premises regular-preserved-by-jump%false)
    (apply-macete-with-minor-premises regular-preserved-by-append)
    (apply-macete-with-minor-premises regular-preserved-by-jump)
    simplify)))

(def-theorem run_flat-append
  "forall(f_0:[nn,instr_f], f_seq_q{f_0} and regular%instr_f(f_0)
 implies
 forall(f_1:[nn,instr_f],s:state, 
  run_flat(append{f_0,f_1},s)== run_flat(f_1,run_flat(f_0,s))))"
  (theory flattener)
  (proof
   (

    (cut-with-single-formula "forall(f_0:[nn,instr_f],
  f_seq_q{f_0} and regular%instr_f(f_0)
   implies 
  forall(n:nn,f_1:[nn,instr_f],s:state,
    run_flat(append{drop{f_0,n},f_1},s)
    ==run_flat(f_1,run_flat(drop{f_0,n},s))))")
    (block (script-comment "having introduced the *right* induction hypothesis, 
we next show that it entails the theorem.")
	   direct-and-antecedent-inference-strategy
	   (auto-instantiate-universal-antecedent
	    "with(p:prop, forall(f_0:[nn,instr_f], p))")
	   (instantiate-universal-antecedent
	    "with(p:prop,forall(n:nn,f_1:[nn,instr_f],s:state,p));"
	    ("0" "f_1" "s"))
	   (simplify-antecedent "with(s:state,f,f_1:[nn,instr_f],
  not(#(run_flat(f_1,run_flat(f,s)))));")
	   (simplify-antecedent "with(s:state,s=s);"))
    (induction flattener_seq-inductor ("f_0"))
    (antecedent-inference "with(p:prop,p implies p);")
    (block (script-comment "Observe that s_$0 is regular.")
	   (contrapose "with(p:prop,not(p));")
	   (force-substitution "s_$0" "drop{(cons{e,s_$0}),1}" (0))
	   (apply-macete-with-minor-premises regular-preserved-by-drop)
	   simplify)
    (case-split ("n_$2=0"))
    (move-to-sibling 2)
    (block (script-comment "Consider the case with n_$2>0.")
	   (apply-macete-with-minor-premises drop-cons-and-simplify))
    (script-comment "Consider next n_$2=0.")
    simplify
    (instantiate-theorem instr_f-cases_flattened-instructions ("e"))
    (block (script-comment
	    "Consider the first subcase, a non-control instruction.")
	   (force-substitution "e " "nc (nc_instr(e))" (0 1))
	   (apply-macete-with-minor-premises run_flat-non-control)
	   (instantiate-universal-antecedent
	    "with(p:prop,forall(n:nn,f_1:[nn,instr_f],s:state,p));"
	    ("0" "f_$0" "next (s_$1,nc_instr(e))"))
	   (move-to-ancestor 2)
	   simplify)
    (block (script-comment
	    "Consider the next subcase, a jump instruction.")
	   (force-substitution "e " "jump (jump_length(e))" (0 1))
	   (apply-macete-with-minor-premises run_flat-jump)
	   (apply-macete-with-minor-premises tr%drop-some-from-append)
	   (instantiate-universal-antecedent
	    "with(p:prop,forall(n:nn,f_1:[nn,instr_f],s:state,p));"
	    ("jump_length(e)" "f_$0" "s_$1"))
	   (force-substitution "jump_length(e)<=length{s_$0}"
			       "0+jump_length(e)<1+length{s_$0}"
			       (0))
	   justify-forced-substitution
	   (apply-macete-with-minor-premises regular-jump_length-macete)
	   auto-instantiate-existential
	   simplify
	   simplify)
    (block (script-comment
	    "Consider the last main subcase, a jump%false instruction.")
	   (force-substitution "e " "jump%false(jumpf_length(e))" (0 1))
	   (apply-macete-with-minor-premises run_flat-jump%false)
	   (apply-macete-with-minor-premises tr%drop-some-from-append)
	   (case-split-on-conditionals (0))
	   (block (script-comment
		   "Suppose the state is truthful -- i.e. no jump occurs.")
		  (instantiate-universal-antecedent
		   "with(p:prop,forall(n:nn,f_1:[nn,instr_f],s:state,p));"
		   ("0" "f_$0" "s_$1"))
		  (move-to-ancestor 2)
		  simplify)
	   (block (script-comment
		   "Suppose the state is not truthful, so a jump occurs.")
		  (apply-macete-with-minor-premises tr%drop-some-from-append)
		  (force-substitution "jumpf_length(e)<=length{s_$0}"
				      "0+jumpf_length(e)<1+length{s_$0}"
				      (0))
		  justify-forced-substitution
		  (apply-macete-with-minor-premises regular-jumpf_length-macete)
		  auto-instantiate-existential
		  simplify
		  simplify)))))

;; Main theorem:

(def-theorem flattener-correct
  "forall(c:code, s:state, run_flat(flatten(c),s)=run_code(c)(s))"
  (theory flattener)
  (proof
   (
    (cut-with-single-formula "forall(c:code,forall(s:state,
  run_flat(flatten(c),s)=run_code(c)(s)));")
    simplify
    (induction code-code-inductor ("c"))
    (case-split-on-conditionals (0))
    (block (script-comment "Case where state is truthful -- i.e. no jump is taken.")
	   (apply-macete-with-minor-premises run_flat-append)
	   (apply-macete-with-minor-premises run_flat-jump)
	   (apply-macete-with-minor-premises tr%drop-some-from-append)
	   (apply-macete-with-minor-premises tr%drop-all-or-more)
	   simplify)
    (block (script-comment "Case where state is non-truthful, so a jump is taken.")
	   (force-substitution
	    "append{flatten(y%unless%false_0),
		    cons{jump(length{flatten(y%unless%false_1)}),
                            append{flatten(y%unless%false_1),
                                   flatten(y%unless%false_2)}}}"
	    "append{append{flatten(y%unless%false_0),
                       cons{jump(length{flatten(y%unless%false_1)}),nil{instr_f}}},
                            append{flatten(y%unless%false_1),
                                   flatten(y%unless%false_2)}}"
	    (0))
	   justify-forced-substitution
	   (apply-macete-with-minor-premises tr%drop-some-from-append)
	   (apply-macete-with-minor-premises tr%drop-all-or-more)
	   (apply-macete-with-minor-premises tr%append-nil)
	   (apply-macete-with-minor-premises run_flat-append)
	   simplify
	   (apply-macete-with-minor-premises sequence-length)
	   (apply-macete-with-minor-premises sequence-length)))))








