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


; 
; 			 
;			 INDICATORS EXERCISE
;
;
; 0. Load the section of the theory library called FOUNDATION by
; evaluating

(load-section foundation)

;
; 1. Introduction
;
; An indicator is a function used to represent a set.  It has a sort
; of the form [alpha -> unit%sort] (also written more simply as
; [alpha,unit%sort]), where alpha is an arbitrary sort.  (In the
; string syntax, the sort [alpha -> unit%sort] is printed as
; sets[alpha].)  unit%sort is a sort of THE-KERNEL-THEORY that
; contains exactly one element named an%individual.  unit%sort is of
; kind ind, so indicators may be partial functions.  Since
; THE-KERNEL-THEORY is a component theory of every IMPS theory,
; unit%sort is available in every theory.
;
; Indicators are convenient for representing sets.  The basic idea is
; that a set s containing objects of sort alpha can be represented by
; an indicator of sort [alpha -> unit%sort] whose domain is s itself.
; Simplifying expressions involving indicators is to a large extent a
; matter of checking definedness -- for which the simplifier is
; equipped with special-purpose algorithms.  The theory INDICATORS
; consists of just a single base sort uu, for "universe".  Since
; INDICATORS contains no constants nor axioms, theory interpretations
; of INDICATORS are trivial to construct, and thus theorems of
; INDICATORS are easy to use as transportable macetes.
;
; The machinery for building indicators consists entirely of the
; following table of quasi-constructors:
;
; 
; Official name                  String syntax
; ----------------------------------------------------------------------
; predicate-to-indicator         indic             (binder)
; sort-to-indicator              sort_to_indic     (prefix)
; i-in                           in                (infix)
; i-subseteq                     subseteq          (infix)
; i-subset                       subset            (infix)
; i-empty-indicator              empty_indic       (prefix)
; i-nonempty-indicator?          nonempty_indic_q  (prefix)
; i-empty-indicator?             empty_indic_q     (prefix)
; i-complement                   ^^                (postfix)
; i-union                        union             (infix)
; i-intersection                 inters            (infix)
; i-difference                   diff              (infix)
; i-sym-difference               sym_diff          (infix)
; i-disjoint                     disj              (infix)
; i-partition?                   partition_q       (prefix)
; i-singleton                    singleton         (prefix)
; 
;
; The definitions of these quasi-constructors are located in the file
; theories/generic-theories/indicators.t
; 
; 
; 2. Tips on Proving Theorems about Indicators
; 

; When proving properties about any quasi-constructor, it is usually
; essential to get at the "guts" of the quasi-constructor.  This is
; done in IMPS by using the "insistent" commands:
; 
;   antecedent-inference
;   antecedent-inference-strategy
;   beta-reduce-insistently
;   insistent-direct-inference
;   insistent-direct-inference-strategy
;   simplify-insistently
; 
; Each of the last four commands is equivalent to "disabling" all
; quasi-constructors and then applying the corresponding noninsistent
; command.
;
; Many properties about indicators are provable with just one
; application of simplify-insistently.  Extensionality and
; case-split-on-conditionals are two other commands that are often
; useful for proving statements about indicators.
;
; We will work in the theory INDICATORS which contains
; THE-KERNEL-THEORY plus the base sort uu.  Set the current theory to
; this theory using the command found in the "General" menu or by
; evaluaing

(set (current-theory) (name->theory 'indicators))

;
; 3. Some Simple Indicator Lemmas
;
; We will start off by proving a few simple facts about indicators:
 
(def-theorem empty_indic-is-empty
  "empty_indic_q{empty_indic{uu}}"
  (theory indicators)
  (usages transportable transportable-rewrite)
  (proof
   (

    simplify-insistently

    )))

(def-theorem union-commutativity
  "forall(a,b:sets[uu], (a union b) = (b union a))"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (

    direct-inference
    extensionality
    direct-inference
    simplify-insistently

    )))

(def-theorem element-of-a-subset-is-an-element 		; 
  "forall(x:uu,b:sets[uu], 
     forsome(a:sets[uu], (x in a) and (a subseteq b))
       implies 
     (x in b))"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(b,a:sets[uu],a subseteq b)" 
     ("x"))

    )))

(def-theorem subseteq-transitivity 
  "forall(a,b,c:sets[uu], 
     (a subseteq b) and (b subseteq c) implies (a subseteq c))"
  (theory indicators)
  (usages transportable-macete)
  (proof 
   (

    insistent-direct-inference-strategy 
    simplify-insistently

    )))

(def-theorem subseteq-antisymmetry
  "forall(a,b:sets[uu],  
     a = b iff ((a subseteq b) and (b subseteq a)))"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (

    insistent-direct-inference-strategy
    (force-substitution "b" "a" (0))
    (force-substitution "a" "b" (0))
    (block 
      (script-comment 
       "`insistent-direct-inference-strategy' at (0 1)") 
      extensionality
      direct-inference 
      (antecedent-inference "with(p:prop,p);")
      (instantiate-universal-antecedent 
       "with(a,b:sets[uu],b subseteq a);" 
       ("x_0"))
      (block 
	(script-comment 
	 "`instantiate-universal-antecedent' at (0 0 0)")
	(instantiate-universal-antecedent 
	 "with(b,a:sets[uu],a subseteq b);" 
	 ("x_0")) 
	simplify
	)
      (block 
	(script-comment 
	 "`instantiate-universal-antecedent' at (0 0 1)")
	(instantiate-universal-antecedent 
	 "with(b,a:sets[uu],a subseteq b);" 
	 ("x_0")) 
	simplify))

    )))
 
; This last theorem is often useful for proving the equivalence of
; indicators.  
; 
;
; 4. A Macete for Intervals of Integers
; 
; Set the current theory to H-O-REAL-ARITHMETIC using the command
; found in the "General" menu or by evaluaing

(set (current-theory) (name->theory 'h-o-real-arithmetic))

; and then prove the following little facts about integer intervals.
; (Hint: use subseteq-antisymmetry as a transportable macete.) 

(def-theorem trivial-interval
  "forall(m,n:zz, 
     m=n 
      implies
     indic{x:zz, m<=x and x<=n} = singleton{m})"
  (theory h-o-real-arithmetic)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-inference
    (block 
      (script-comment "`direct-inference' at (0)") 
      insistent-direct-inference simplify)
    (block 
      (script-comment "`direct-inference' at (1)") 
      insistent-direct-inference simplify)

    )))

(def-theorem shorten-interval
  "forall(m,n:zz, 
     m<n 
      implies 
     indic{x:zz, m<=x and x<=n} = 
     singleton{m} union indic{x:zz, m+1<=x and x<=n})"
  (theory h-o-real-arithmetic)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-inference
    (block 
      (script-comment "`direct-inference' at (0)") 
      insistent-direct-inference 
      simplify)
    (block 
      (script-comment "`direct-inference' at (1)") 
      insistent-direct-inference 
      simplify
      direct-and-antecedent-inference-strategy 
      simplify 
      simplify 
      simplify)

    )))

(def-theorem empty-interval
  "forall(m,n:zz, 
     n<m
      implies
     indic{x:zz, m<=x and x<=n} = empty_indic{zz})"
  (theory h-o-real-arithmetic)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-inference
    (block 
      (script-comment "`direct-inference' at (0)") 
      insistent-direct-inference 
      simplify)
    (block 
      (script-comment "`direct-inference' at (1)") 
      insistent-direct-inference 
      simplify)

    )))

; Build a macete with

(def-compound-macete transform-interval
  (without-minor-premises
   (series
    empty-interval
    (repeat shorten-interval)
    trivial-interval
    simplify)))
   
; Apply this macete to 
 
(view-expr "with(y:sets[zz], y=indic{x:zz, 3<=x and x<=6})")
 
; Also, apply the macete to
 
(view-expr "with(y:sets[zz], y=indic{x:zz, 7<=x and x<=6})")

;
; 			   END OF EXERCISE






