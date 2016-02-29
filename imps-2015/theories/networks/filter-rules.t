(include-files
  (files (imps theories/networks/single-filter)
	 (imps theories/generic-theories/boole)))

(def-cartesian-product filter%rules
  (directions 
   "sets[addresses]" 
   "sets[addresses]" 
   "sets[protocols]"
   "sets[ports]" 
   "sets[ports]" 
   boole
   "[filtered%states,datagrams -> boole]"
   boole)
  (constructor make%filter%rule)
  (accessors fr%direction
	     fr%source%addresses
	     fr%destination%addresses
	     fr%protocols
             fr%source%ports
             fr%destination%ports
	     fr%can%initiate%tcp%connection
	     fr%state%condition
	     fr%action)
  (theory single-filter-theory))

(def-constant check%fr%condition
  "lambda(r:filter%rules, d:datagrams, b:directions, s:filtered%states,
     b = fr%direction(r) 
      and
     source%address(d) in fr%source%addresses(r)
      and
     destination%address(d) in fr%destination%addresses(r)
      and
     protocol(d) in fr%protocols(r)
      and
     source%port(d) in fr%source%ports(r)
      and
     destination%port(d) in fr%destination%ports(r)
      and
     (initiates%tcp%connection(d) 
       implies 
      is%true(fr%can%initiate%tcp%connection(r)))
      and
     is%true(fr%state%condition(r)(s,d)))"
  (theory single-filter-theory))

(def-constant make%zero%rule%filter%module
  "lambda(d:datagrams,b:directions,s:filtered%states,else:prop,else)"
  (theory single-filter-theory))

(def-constant make%one%rule%filter%module
  "lambda(r:filter%rules,
     lambda(d:datagrams,b:directions,s:filtered%states,else:prop,
       if(check%fr%condition(r,d,b,s), 
        is%true(fr%action(r)),
        else)))"
  (theory single-filter-theory))

(def-constant make%two%rule%filter%module
  "lambda(r_1,r_2:filter%rules,
     lambda(d:datagrams,b:directions,s:filtered%states,else:prop,
       if(check%fr%condition(r_1,d,b,s), 
        is%true(fr%action(r_1)),
        check%fr%condition(r_2,d,b,s), 
        is%true(fr%action(r_2)),
        else)))"
  (theory single-filter-theory))

(def-constant make%three%rule%filter%module
  "lambda(r_1,r_2,r_3:filter%rules,
     lambda(d:datagrams,b:directions,s:filtered%states,else:prop,
       if(check%fr%condition(r_1,d,b,s), 
        is%true(fr%action(r_1)),
        check%fr%condition(r_2,d,b,s), 
        is%true(fr%action(r_2)),
        check%fr%condition(r_3,d,b,s), 
        is%true(fr%action(r_3)),
        else)))"
  (theory single-filter-theory))

(def-constant null%state%condition
  "lambda(s:filtered%states, d:datagrams, true%val)"
  (theory single-filter-theory))

(def-theorem null_state_condition-is-always-true
  "forall(s:filtered%states, d:datagrams, 
     is%true(null%state%condition(s,d)) iff truth)"
  (usages rewrite)
  (theory single-filter-theory)
  (proof
   (

    unfold-defined-constants

    )))

(def-constant compose%filter%modules
  "lambda(m_1,m_2:[datagrams, directions, filtered%states, prop -> prop],
     lambda(d:datagrams, b:directions, s:filtered%states, else:prop,
       m_1(d,b,s,m_2(d,b,s,else))))"
  (theory single-filter-theory))