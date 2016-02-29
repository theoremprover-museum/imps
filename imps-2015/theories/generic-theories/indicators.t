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


(herald INDICATORS)

;;; No required files


;;; Build theory of indicators

(def-language INDICATORS-LANGUAGE
  (embedded-language the-kernel-language)
  (base-types uu))

(def-theory INDICATORS
  (language indicators-language))
  

;;; Build theory of family indicators

(def-language INDEX-LANGUAGE
  (embedded-language indicators-language)
  (base-types index))

(def-theory FAMILY-INDICATORS
  (language index-language)
  (component-theories indicators))


;;; Parse specifications

(def-parse-syntax predicate-to-indicator
  (token indic)
  (null-method parse-indicator-constructor-both-syntaxes) 
  (binding 50))

(def-parse-syntax predicate-to-indicator
  (token pred_to_indic)
  (null-method prefix-operator-method) 
  (binding 160))

(def-parse-syntax sort-to-indicator
  (token sort_to_indic)
  (null-method prefix-sort-dependent-operator-method) 
  (binding 160))

(def-parse-syntax i-in
  (token in)
  (null-method null-call-method-terminator)
  (left-method infix-operator-method) 
  (binding 101))

(def-parse-syntax i-subseteq
  (token subseteq)
  (left-method infix-operator-method) 
  (binding 101))

(def-parse-syntax i-subset
  (token subset)
  (left-method infix-operator-method) 
  (binding 101))

(def-parse-syntax i-empty-indicator
  (token empty_indic)
  (null-method prefix-sort-dependent-operator-method) 
  (binding 160))

(def-parse-syntax i-nonempty-indicator?
  (token nonempty_indic_q)
  (null-method prefix-operator-method) 
  (binding 160))

(def-parse-syntax i-empty-indicator?
  (token empty_indic_q)
  (null-method prefix-operator-method) 
  (binding 160))

(def-parse-syntax i-complement
  (token ^^)
  (left-method postfix-operator-method) 
  (binding 164))

(def-parse-syntax i-union
  (token union)
  (left-method infix-operator-method) 
  (binding 162))

(def-parse-syntax i-intersection
  (token inters)
  (left-method infix-operator-method) 
  (binding 163))

(def-parse-syntax i-difference
  (token diff)
  (left-method infix-operator-method) 
  (binding 102))

(def-parse-syntax i-sym-difference
  (token sym_diff)
  (left-method infix-operator-method) 
  (binding 103))

(def-parse-syntax i-disjoint
  (token disj)
  (left-method infix-operator-method) 
  (binding 104))

(def-parse-syntax i-big-union
  (token big_u)
  (null-method prefix-operator-method) 
  (binding 160))

(def-parse-syntax i-big-intersection
  (token big_i)
  (null-method prefix-operator-method) 
  (binding 160))

(def-parse-syntax i-partition?
  (token partition_q)
  (null-method prefix-operator-method) 
  (binding 160))

(def-parse-syntax i-singleton
  (token singleton)
  (null-method prefix-operator-method) 
  (binding 160))


;;; Print specifications

(def-print-syntax predicate-to-indicator
  (token (indic pred_to_indic))
  (method present-indicator-constructor-operator)
  (binding 50))

(def-print-syntax sort-to-indicator
  (token sort_to_indic)
  (method present-sort-dependent-prefix-operator) 
  (binding 160))

(def-print-syntax i-in
  (token " in ")
  (method present-binary-infix-operator) 
  (binding 101))

(def-print-syntax i-subseteq
  (token " subseteq ")
  (method present-binary-infix-operator) 
  (binding 101))

(def-print-syntax i-subset
  (token " subset ")
  (method present-binary-infix-operator) 
  (binding 101))

(def-print-syntax i-empty-indicator
  (token empty_indic)
  (method present-sort-dependent-prefix-operator)
  (binding 160))

(def-print-syntax i-nonempty-indicator?
  (token nonempty_indic_q)
  (method present-prefix-operator)
  (binding 101))

(def-print-syntax i-empty-indicator?
  (token empty_indic_q)
  (method present-prefix-operator)
  (binding 101))

(def-print-syntax i-complement
  (token ^^)
  (method present-postfix-operator)
  (binding 164))

(def-print-syntax i-union
  (token " union ")
  (method present-binary-infix-operator)
  (binding 162))

(def-print-syntax i-intersection
  (token " inters ")
  (method present-binary-infix-operator)
  (binding 163))

(def-print-syntax i-difference
  (token " diff ")
  (method present-binary-infix-operator)
  (binding 102))

(def-print-syntax i-sym-difference
  (token " sym_diff ")
  (method present-binary-infix-operator)
  (binding 103))

(def-print-syntax i-disjoint
  (token " disj ")
  (method present-binary-infix-operator)
  (binding 104))

(def-print-syntax i-big-union
  (token big_u)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax i-big-intersection
  (token big_i)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax i-partition?
  (token partition_q)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax i-singleton
  (token singleton)
  (method present-prefix-operator)
  (binding 160))


;;; TeX print specifications

(def-print-syntax predicate-to-indicator
  tex
  (token (indic pred%to%indic))
  (method present-tex-indicator-constructor-operator)
  (binding 50))

(def-print-syntax sort-to-indicator
  tex
  (token sort%indicator)
  (method present-tex-sort-dependent-prefix-operator)
  (binding 160))

(def-print-syntax i-in
  tex
  (token " \\in ")
  (method present-tex-binary-infix-operator)
  (binding 101))

(def-print-syntax i-subseteq
  tex
  (token " \\subseteq ")
  (method present-tex-binary-infix-operator)
  (binding 101))

(def-print-syntax i-subset
  tex
  (token " \\subset ")
  (method present-tex-binary-infix-operator)
  (binding 101))

(def-print-syntax i-empty-indicator
  tex
  (token " \\emptyset ")
  (method present-tex-symbol)
  (binding 101))

(def-print-syntax i-nonempty-indicator?
  tex
  (token "\\mbox{ \\rm nonempty } ")
  (method present-tex-prefix-operator)
  (binding 160))

(def-print-syntax i-empty-indicator?
  tex
  (token "\\mbox{ \\rm empty } ")
  (method present-tex-prefix-operator)
  (binding 160))

(def-print-syntax i-complement
  tex
  (token "{ \\bf C} ")
  (method present-loglike-operator)
  (binding 161))

(def-print-syntax i-union
  tex
  (token " \\cup ")
  (method present-tex-binary-infix-operator)
  (binding 162))

(def-print-syntax i-intersection
  tex
  (token " \\cap ")
  (method present-tex-binary-infix-operator)
  (binding 163))

(def-print-syntax i-difference
  tex
  (token " \\setminus ")
  (method present-tex-binary-infix-operator)
  (binding 164))

(def-print-syntax i-disjoint
  tex
  (token " \\,\\acute{o}\\, ")
  (method present-tex-binary-infix-operator)
  (binding 101))

(def-print-syntax i-singleton
  tex
  (token (" \\{ " " \\} "))
  (method present-tex-delimited-expression)
  (binding 101))

(def-print-syntax i-big-union
  tex
  (token " \\bigcup " )
  (method present-tex-prefix-operator)
  (binding 160))

(def-print-syntax i-big-intersection
  tex
  (token " \\bigcap " )
  (method present-tex-prefix-operator)
  (binding 160))

;;; Indicator quasi-constructors for sets

(def-quasi-constructor PREDICATE-TO-INDICATOR
  "lambda(s:[uu,prop], lambda(x:uu, if(s(x), an%individual, ?unit%sort)))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor SORT-TO-INDICATOR
  "lambda(e:uu, lambda(x:uu, an%individual))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-IN
  "lambda(x:uu,a:sets[uu], #(a(x)))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-SUBSETEQ
  "lambda(a,b:sets[uu], forall(x:uu, (x in a) implies (x in b)))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-SUBSET
  "lambda(a,b:sets[uu], (a subseteq b) and not(a = b))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-EMPTY-INDICATOR
  "lambda(e:uu, lambda(x:uu,?unit%sort))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-NONEMPTY-INDICATOR?
  "lambda(a:sets[uu], forsome(x:uu, x in a))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-EMPTY-INDICATOR?
  "lambda(a:sets[uu], forall(x:uu, not(x in a)))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-COMPLEMENT
  "lambda(s:sets[uu], indic(x:uu, (not #(s(x)))))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-UNION
  "lambda(s,t:sets[uu], indic(x:uu, #(s(x)) or #(t(x))))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-INTERSECTION
  "lambda(s,t:sets[uu], indic(x:uu, #(s(x)) and #(t(x))))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-DIFFERENCE
  "lambda(s,t:sets[uu], indic(x:uu, #(s(x)) and (not #(t(x)))))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-SYM-DIFFERENCE
  "lambda(s,t:sets[uu],
      indic(x:uu, (#(s(x)) and (not #(t(x)))) or ((not #(s(x))) and #(t(x)))))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-DISJOINT
  "lambda(s,t:sets[uu], forall(x:uu, not(x in s) or not(x in t)))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-PARTITION?
  "lambda(w:sets[sets[uu]],s:sets[uu],
     forall(u,v:sets[uu], 
       ((not (u = v)) and (u in w) and (v in w)) implies (u disj v)) and 
     forall(x:uu, (x in s) iff forsome(u:sets[uu], (u in w) and (x in u))))"
  (language indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-SINGLETON
  "lambda(a:uu, indic(x:uu, x=a))"
  (language indicators)
  (fixed-theories the-kernel-theory))
  

;;; Indicator quasi-constructors for families of sets

(def-quasi-constructor I-BIG-UNION
  "lambda(f:[index,sets[uu]], indic(x:uu, forsome(i:index, #(f(i)(x)))))"
  (language family-indicators)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor I-BIG-INTERSECTION
  "lambda(f:[index,sets[uu]], indic(x:uu, forall(i:index, #(f(i)(x)))))"
  (language family-indicators)
  (fixed-theories the-kernel-theory))


;;; Preliminary lemmas

(def-theorem VALUE-OF-A-DEFINED-INDICATOR-APPLICATION
  "forall(a:sets[uu],x:uu, (x in a) implies a(x) = an%individual)"
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify)))

(def-theorem MEANING-OF-INDIC-FROM-PRED-ELEMENT
  "forall(x:uu,p:[uu,prop], (x in pred_to_indic(p)) iff p(x))"
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify)))

(def-theorem MEANING-OF-INDIC-FROM-SORT-ELEMENT
  "forall(x:uu, (x in sort_to_indic(uu)) iff #(x,uu))"
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify-insistently)))


