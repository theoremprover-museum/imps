(include-files
  (files (imps theories/networks/filter-rules)))

;;; Deny all policy

(def-constant deny%all%inbound%rule
  "make%filter%rule(inbound,
                    indic{a:addresses, truth},
                    indic{a:addresses, truth},
                    indic{p:protocols, truth},
                    indic{p:ports, truth},
                    indic{p:ports, truth},
                    true%val,
                    null%state%condition,
                    false%val)"
  (theory single-filter-theory))

(def-constant deny%all%outbound%rule
  "make%filter%rule(outbound,
                    indic{a:addresses, truth},
                    indic{a:addresses, truth},
                    indic{p:protocols, truth},
                    indic{p:ports, truth},
                    indic{p:ports, truth},
                    true%val,
                    null%state%condition,
                    false%val)"
  (theory single-filter-theory))

(def-constant deny%all%module
  "make%two%rule%filter%module(deny%all%inbound,deny%all%inbound)"
  (theory single-filter-theory))

(def-theorem deny_all_module-correctness
  "forall(d:datagrams,b:directions,s:filtered%states,else:prop,
     filter(d,b,s) iff deny%all%module(d,b,s,else))
    implies
   forall(d:datagrams,b:directions,s:filtered%states, 
     not(filter(d,b,s)))"
  (theory single-filter-theory)
  (proof
   (

    unfold-defined-constants
    (unfold-single-defined-constant-globally make%two%rule%filter%module)
    (unfold-single-defined-constant-globally deny%all%inbound)
    (unfold-single-defined-constant-globally deny%all%outbound)
    (unfold-single-defined-constant-globally check%fr%condition)
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(p:prop,p);" 
     ("d" "b" "s" "else"))
    (instantiate-theorem 
     every-direction-is-inbound-or-outbound 
     ("b"))

    )))

;;; No spoofing policy

(def-constant no%spoofing%policy
  "forall(d:datagrams, s:filtered%states,
     source%address(d) in internal
      implies
     not(filter(d,inbound,s)))"
  (theory single-filter-theory))

(def-constant no%spoofing%rule
  "make%filter%rule(inbound,
                    internal,
                    indic{a:addresses, truth},
                    indic{p:protocols, truth},
                    indic{p:ports, truth},
                    indic{p:ports, truth},
                    true%val,
                    null%state%condition,
                    false%val)"
  (theory single-filter-theory))

(def-constant no%spoofing%module
  "make%two%rule%filter%module(no%spoofing%rule)"
  (theory single-filter-theory))

(def-theorem no_spoofing_module-correctness
  "forall(d:datagrams,b:directions,s:filtered%states,else:prop,
     filter(d,b,s) iff no%spoofing%module(d,b,s,else))
    implies
   no%spoofing%policy"
  (theory single-filter-theory)
  (proof
   (

    unfold-defined-constants
    (unfold-single-defined-constant-globally make%one%rule%filter%module)
    (unfold-single-defined-constant-globally no%spoofing%rule)
    (unfold-single-defined-constant-globally check%fr%condition)
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(p:prop,
        forall(d:datagrams,b:directions,s:filtered%states,else:prop,p));"
     ("d" "inbound" "s" "else"))

    )))


;;; Limited externally initiated tcp connections policy

(def-constant no%externally%initiated%tcp%connections
  "forall(d:datagrams, s:filtered%states,
     source%address(d) in external
      and
     destination%address(d) in internal
      and
     initiates%tcp%connection(d)
      implies
     not(filter(d,inbound,s)))"
  (theory single-filter-theory))

(def-constant limited%externally%initiated%tcp%connections
  "lambda(servers:sets[addresses],
     forall(d:datagrams, s:filtered%states,
       source%address(d) in external
        and
       destination%address(d) in (internal diff servers)
        and
       initiates%tcp%connection(d)
        implies
       not(filter(d,inbound,s))))"
  (theory single-filter-theory))
     
     



