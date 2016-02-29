(herald evaluation)

(def-language language-op-semantics
  (base-types state value expr)
  (constants 
   (op%state (expr state state))
   (op%value (expr state value))))


(def-theory op-semantics
  (language language-op-semantics)
  (component-theories h-o-real-arithmetic))

(load-section sequences)

(def-atomic-sort expr%seq
  "lambda(f:[nn,expr], f_seq_q{f})"
  (theory op-semantics)
  (witness "lambda(x:nn, ?expr)"))

(def-atomic-sort state%seq
  "lambda(f:[nn,state], f_seq_q{f})"
  (theory op-semantics)

  (witness "lambda(x:nn, ?state)"))

(def-recursive-constant opseq%state
  "lambda(evs:[state, expr%seq, nn -> state], 
       lambda(env:state, f:expr%seq, n:nn, 
                      if(n=0, op%state(f(0), env),
                         op%state(f(n), evs(env, f, n-1)))))"
  (theory op-semantics))
 
'(def-theorem seq%state-length
  "forall(s:state, f:expr%seq,n:nn, 
    #(opseq%state(s,f,n)) iff (n<length(f) and forall(j:nn, j<n implies #(opseq%state(s,f,n)))))"
  (theory op-semantics)
  (proof
   (



    (cut-with-single-formula "forall(s:state,f:expr%seq,n:zz, 0<=n implies (#(seq%state(s,f,n)) iff n<length{f}))")
    simplify
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (induction complete-inductor ("n"))
      (incorporate-antecedent "with(p:prop,forall(k:zz,p));")
      (apply-macete-with-minor-premises tr%meaning-of-length)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
	direct-and-antecedent-inference-strategy
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
	  (case-split ("m_$0=0"))
	  (simplify-antecedent "with(s:state,#(s));")
	  (simplify-antecedent "with(s:state,#(s));"))
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
	  (case-split ("m_$0=0"))
	  simplify
	  (block 
	    (script-comment "`case-split' at (2)")
	    simplify
	    (backchain-backwards "with(p:prop,forall(k:zz,p));")
	    simplify
	    (apply-macete-with-minor-premises tr%sequence-defined-monotonically)
	    (instantiate-existential ("m_$0"))
	    (apply-macete-with-minor-premises expr%seq-in-quasi-sort_op-semantics)
	    simplify)))
      (apply-macete-with-minor-premises expr%seq-in-quasi-sort_op-semantics)
      (apply-macete-with-minor-premises expr%seq-in-quasi-sort_op-semantics))
    )))
)