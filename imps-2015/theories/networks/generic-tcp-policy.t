(include-files
  (files (imps theories/networks/filter-rules)))

(def-language generic-tcp-lang
  (embedded-language single-filter-theory)
  (constants
   (direction        directions)
   (initiators       "sets[addresses]")
   (responders       "sets[addresses]")
   (initiator%ports  "sets[ports]")
   (responder%ports  "sets[ports]")))

(def-theory generic-tcp-theory
  (language generic-tcp-lang)
  (component-theories single-filter-theory))

(def-constant generic%tcp%connection
  "lambda(s_1:states,s_2:filtered%states,f:[nn -> nn],
          a_1,a_2:addresses,p_1,p_2:ports,
     tcp%connection(s_1,s_2,f,a_1,a_2,p_1,p_2)
      and
     a_1 in initiators
      and
     a_2 in responders
      and 
     p_1 in initiator%ports
      and
     p_2 in responder%ports)"
  (theory generic-tcp-theory))

(def-constant every%tcp%connection%is%generic
  "forall(s_1:states,s_2:filtered%states,f:[nn -> nn],
          a_1,a_2:addresses,p_1,p_2:ports,
    tcp%connection(s_1,s_2,f,a_1,a_2,p_1,p_2) 
     implies
    generic%tcp%connection(s_1,s_2,f,a_1,a_2,p_1,p_2))"
  (theory generic-tcp-theory))

(def-constant generic%tcp%rule%1
  "make%filter%rule(direction,
                    initiators,
                    responders,
                    singleton{tcp},
                    initiator%ports,
                    responder%ports,
                    true%val,
                    null%state%condition,
                    true%val)"
  (theory generic-tcp-theory))

(def-constant generic%tcp%rule%2
  "make%filter%rule(opposite%direction(direction),
                    responders,
                    initiators,
                    singleton{tcp},
                    responder%ports,
                    initiator%ports,
                    false%val,
                    null%state%condition,
                    true%val)"
  (theory generic-tcp-theory))

(def-constant generic%tcp%filter%module
  "make%two%rule%filter%module(generic%tcp%rule%1,generic%tcp%rule%2)"
  (theory generic-tcp-theory))

(def-theorem generic_tcp_filter_module-correctness
  "forall(d:datagrams,b:directions,s:filtered%states,
     filter(d,b,s) iff generic%tcp%filter%module(d,b,s,falsehood))
    implies 
   every%tcp%connection%is%generic"
  (theory generic-tcp-theory)
  (proof
   (

    unfold-defined-constants
    (unfold-single-defined-constant-globally make%two%rule%filter%module)
    (unfold-single-defined-constant-globally generic%tcp%connection)
    direct-inference
    direct-inference
    direct-inference
    simplify
    (instantiate-theorem 
     first-datagram-in-tcp_connection-lemma
     ("s_1" "s_2" "f" "a_1" "a_2" "p_1" "p_2"))
    (instantiate-theorem 
     tcp_connection-embedding-lemma
     ("s_1" "s_2" "f" "a_1" "a_2" "p_1" "p_2" "0"))
    (instantiate-theorem 
     filtered_states-defining-axiom-lemma 
     ("s_2" "f(0)"))
    (incorporate-antecedent 
     "with(p_2,p_1:ports,a_2,a_1:addresses,f:datagrams,
        has%profile(f,a_1,a_2,p_1,p_2,tcp));")
    (unfold-single-defined-constant-globally has%profile)
    direct-inference
    (cut-with-single-formula 
     "#(takefirst{s_2,f(0)},filtered%states)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (instantiate-universal-antecedent 
       "with(p:prop,
          forall(d:datagrams,b:directions,s:filtered%states,p));"
       ("s_2(f(0))" "b" "takefirst{s_2,f(0)}"))
      (incorporate-antecedent "with(p:prop,if(p, p, p));")
      simplify
      (backchain-backwards "with(p:prop,p and p and p and p and p);")
      (backchain-backwards "with(p:prop,p and p and p and p and p);")
      (backchain-backwards "with(p:prop,p and p and p and p and p);")
      (backchain-backwards "with(p:prop,p and p and p and p and p);")
      (force-substitution "s_2(f(0))" "s_1(0)" (0 1))
      (weaken (5 4 3 1))
      (unfold-single-defined-constant-globally generic%tcp%rule%1)
      (unfold-single-defined-constant-globally generic%tcp%rule%2)
      (unfold-single-defined-constant-globally check%fr%condition)
      simplify)
    (apply-macete-with-minor-premises 
     filtered_states-are-closed-under-takefirst)

    )))


;;; Example: Externally initiated SMTP

(def-translation external-smtp
  (source generic-tcp-theory)
  (target single-filter-theory)
  (fixed-theories single-filter-theory)
  (constant-pairs 
   (direction inbound)
   (initiators external)
   (responders internal)
   (initiator%ports "indic{p:ports, p > 1023}")
   (responder%ports "indic{p:ports, p = 25}")
   ))

(def-renamer external-smtp-renamer
  (pairs
   (generic%tcp%connection external%smtp%connection)
   (every%tcp%connection%is%generic
    every%tcp%connection%is%external%smtp)
   (generic%tcp%rule%1 external%smtp%rule%1)
   (generic%tcp%rule%2 external%smtp%rule%2)
   (generic%tcp%filter%module external%smtp%filter%module)))
   
(def-transported-symbols
  (generic%tcp%connection
   every%tcp%connection%is%generic
   generic%tcp%rule%1
   generic%tcp%rule%2
   generic%tcp%filter%module)
  (translation external-smtp)
  (renamer external-smtp-renamer))

(def-theorem external%smpt%filter%module-correctness
  generic_tcp_filter_module-correctness
  ;; "forall(d:datagrams,b:directions,s:filtered%states,
  ;;    filter(d,b,s) iff external%smtp%filter%module(d,b,s,falsehood))
  ;;   implies 
  ;;  every%tcp%connection%is%external%smtp"
  (translation external-smtp)
  (theory single-filter-theory)
  (proof (existing-proof)))


