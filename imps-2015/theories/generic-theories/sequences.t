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


(herald sequences)

;;; This file contains quasi-constructors for sequences.  They may only be used
;;; in theories in which H-O-REAL-ARITHMETIC is a structural sub-theory.  A
;;; sequence is any unary function whose domain is contained in the sort NN.  A
;;; sequence is a finite sequence if its domain is an initial segment of the
;;; natural numbers.  

(load-section basic-real-arithmetic)

;;;(set (proof-log-port) (standard-output))

(def-language sequences-language
  (embedded-language h-o-real-arithmetic)
  (base-types ind_1))

(def-theory sequences
  (language sequences-language)
  (component-theories h-o-real-arithmetic))

(define sequences (name->theory 'sequences))

(define generic-sequences sequences)

(define (SEQUENCE? expr)
  (and (expression? expr)
       (let ((sort (expression-sorting expr)))
	 (and (higher-sort? sort)
	      (ind-sorting? sort)
	      (equal? (length (higher-sort-domains sort)) 1)
	      (eq? (car (higher-sort-domains sort)) 
		   (name->sort (theory-language *ho*) 'nn))))))

(def-quasi-constructor length
 "lambda(s:[nn,ind_1],
	 iota(n:nn,
	  forall(m:nn, m<n iff #(s(m)))))"
  (language sequences)
  (fixed-theories h-o-real-arithmetic))

(define SEQUENCE-LENGTH (name->quasi-constructor 'length))

(def-quasi-constructor f-seq?
  "lambda(s:[nn,ind_1], #(length(s)))"
  (language sequences)
  (fixed-theories h-o-real-arithmetic))

(define FINITE-SEQUENCE? (name->quasi-constructor 'f-seq?))

(def-parse-syntax  f-seq? 
  (token f_seq_q)
  (null-method prefix-operator-method) 
  (binding 160))

(def-print-syntax f-seq?
  TEX
  (token fseq?) 
  (method present-loglike-operator) 
  (binding 160))

(def-print-syntax f-seq?
  (token f_seq_q)
  (method present-prefix-operator) 
  (binding 160))

;; (make-operator *parse* 'f_seq_q 'f-seq? prefix-operator-method '() 160)
;; (make-presentation-format *form* 'f-seq? 'f_seq_q present-prefix-operator 160)
;; (make-presentation-format *tex-form* 'f-seq? 'fseq? present-loglike-operator 160)

(def-quasi-constructor nil
  "lambda(e:ind_1, lambda(n:nn, ?ind_1))"
  (language sequences)
  (fixed-theories h-o-real-arithmetic))

(define SEQUENCE-NIL (name->quasi-constructor 'nil))
(make-quasi-constructor-constantlike sequence-nil)

;; (make-presentation-format *form* 'nil 'nil present-sort-dependent-prefix-operator 160)
;; (make-operator *parse* 'nil 'nil prefix-sort-dependent-operator-method '() 160)
;; (make-presentation-format *tex-form* 'nil " \\langle\\rangle " present-subscripted-sort-arg 160)

(def-parse-syntax nil
  (token nil) 
  (null-method prefix-sort-dependent-operator-method)	
  (binding 160))

(def-print-syntax nil
  TEX
  (token " \\langle\\rangle ") 
  (method present-subscripted-sort-arg) 
  (binding 160))

(def-print-syntax nil
  (token nil) 
  (method present-sort-dependent-prefix-operator) 
  (binding 160))

(def-quasi-constructor cons
  "lambda(e:ind_1, s:[nn,ind_1],  lambda(n:nn, if(n<1, e, s(n-1))))"
  (language sequences)
  (fixed-theories h-o-real-arithmetic))

(define SEQUENCE-CONS (name->quasi-constructor 'cons))
(def-print-syntax cons
   TEX
  (token (" ( " " ) ")) ; a symbol or string. (?!)
  (method present-tex-delimited-expression-with-dots) 
  (binding 80))

;; (make-presentation-format *tex-form* 'cons (list " ( " " ) ") present-tex-delimited-expression-with-dots 80)



(def-quasi-constructor drop
  "lambda(s:[nn,ind_1], n:ind, lambda(m:nn, if(#(n,nn), s(n+m), ?ind_1)))"
  (language sequences)
  (fixed-theories h-o-real-arithmetic))

(define SEQUENCE-DROP (name->quasi-constructor 'drop))
;; (make-presentation-format *tex-form* 'length (list " | " " | ") present-tex-delimited-expression 160)

(def-quasi-constructor takefirst
  "lambda(s:[nn,ind_1], n:ind,
          lambda(m:nn, if(m<n, s(m), ?ind_1)))"
  (language sequences)
  (fixed-theories h-o-real-arithmetic))

(define SEQUENCE-TAKEFIRST (name->quasi-constructor 'takefirst))

(def-quasi-constructor append
  "lambda(s_1,s_2:[nn,ind_1], 
          lambda(m:nn, if(length(s_1)<=m, s_2(m-length(s_1)), s_1(m))))"
  (language sequences)
  (fixed-theories h-o-real-arithmetic))

(define SEQUENCE-APPEND (name->quasi-constructor 'append))

;; (def-quasi-constructor restrict_sq
;;   "lambda(s_1:[nn,ind_1], n:ind,
;;           lambda(m:nn, if(m<n, s_1(m), ?ind_1)))"
;;   (language sequences)
;;   (fixed-theories h-o-real-arithmetic))
;; 
;; (define SEQUENCE-RESTRICT (name->quasi-constructor 'restrict_sq))

(def-quasi-constructor in_seq
  "lambda(x:ind_1, s_1:[nn,ind_1], 
          forsome(i:nn, s_1(i)=x))"
  (language sequences)
  (fixed-theories h-o-real-arithmetic))

(define IN-SEQ (name->quasi-constructor 'in_seq))

;  (define SEQUENCE-POST-CONS
;    (build-quasi-constructor-from-lambda-expression
;     'post-cons
;     (qr "lambda(e:ind_1, s:[nn,ind_1], append(s,cons(e,nil(ind_1))))")
;     (list *ho*)))
;  
;  (disable-quasi-constructor SEQUENCE-POST-CONS)

;;; LEMMAS

(def-theorem meaning-of-zero 
  "forall([[[z],nn]], forall([[[x],nn]], not(x<z)) iff z=0)"
  (theory h-o-real-arithmetic)
  (proof
   (direct-and-antecedent-inference-strategy
    (contrapose "with(z:nn,forall(x:nn,not(x<z)));")
    (instantiate-existential ("0"))
    simplify
    simplify)))

(def-theorem iota-free-definition-of-length
  "forall([[[n],nn],[[s],[nn,ind_1]]], length(s) = n iff
             forall([[[m],nn]], m < n iff #(s(m))))"
  (theory sequences)
  (usages transportable-macete)
  (proof
   (
    (disable-quasi-constructor length)
    direct-and-antecedent-inference-strategy
    (contrapose "with(n:nn,s:[nn,ind_1],
  iota(n:nn,forall(m:nn,m<n iff #(s(m))))=n);")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(s:[nn,ind_1],n:nn,forall(m:nn,m<n iff #(s(m))));" ("m"))
    (contrapose "with(n:nn,s:[nn,ind_1],
  iota(n:nn,forall(m:nn,m<n iff #(s(m))))=n);")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    simplify
    direct-and-antecedent-inference-strategy
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(s:[nn,ind_1],n:nn,forall(m:nn,m<n iff #(s(m))));" ("m"))
    (apply-macete-with-minor-premises eliminate-iota-macete)
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-theorem trichotomy ("b" "n"))
    (instantiate-universal-antecedent "with(s:[nn,ind_1],b:nn,forall(m:nn,m<b iff #(s(m))));" ("n"))
    (instantiate-universal-antecedent "with(s:[nn,ind_1],n:nn,forall(m:nn,m<n iff #(s(m))));" ("n"))
    simplify
    (instantiate-universal-antecedent "with(s:[nn,ind_1],n:nn,forall(m:nn,m<n iff #(s(m))));" ("b"))
    (auto-instantiate-universal-antecedent "with(s:[nn,ind_1],b:nn,forall(m:nn,m<b iff #(s(m))));")
    (instantiate-universal-antecedent "with(s:[nn,ind_1],b:nn,forall(m:nn,m<b iff #(s(m))));" ("b"))
    simplify)))

(def-theorem meaning-of-length
  "forall([[[k],nn],[[s],[nn,ind_1]]], f_seq_q(s) implies 
             k<length(s) iff #(s(k)))"
 (theory sequences)
 (usages transportable-macete)
 (proof
  (direct-inference
   direct-inference
   (instantiate-theorem iota-free-definition-of-length ("length(s)" "s"))
   (backchain "with(s:[nn,ind_1],forall(m:nn,m<length{s} iff #(s(m))));"))))


(def-theorem meaning-of-length-rev 
  "forall([[[k],nn],[[s],[nn,ind_1]]], f_seq_q(s) implies 
             #(s(k)) iff k<length(s))"
 (theory sequences)
 (usages transportable-macete)
 (proof
  (direct-inference
   (instantiate-theorem meaning-of-length ("k" "s"))
   simplify
   simplify
   simplify)))

(def-theorem iota-free-definition-of-length-conv 
  "forall([[[n],nn],[[s],[nn,ind_1]]], forall([[[m],nn]], m < n iff #(s(m))) iff
 		length(s) = n)"
 (theory sequences)
 (usages transportable-macete)
 (proof
  ((assume-theorem iota-free-definition-of-length)
   simplify)))

(def-theorem sequence-defined-up-to-length 
  "forall(s_1:[nn,ind_1],m:nn, 
	 m<length(s_1) 
	 implies
	#(s_1(m)))"
 (theory sequences)
 (usages transportable-macete)
 (proof (direct-and-antecedent-inference-strategy
	 (apply-macete-with-minor-premises meaning-of-length-rev))))

(def-theorem length-characterizes-definedness 
  "forall([[[s],[nn,ind_1]]], #(length(s)) implies 
	forall([[[m],nn]], m < length(s) iff #(s(m))))"
 (theory sequences)
 (usages transportable-macete)
 (proof ((apply-macete-with-minor-premises meaning-of-length))))

(def-theorem sequence-not-defined-at-length 
  "forall([[[s],[nn,ind_1]]], not(#(s(length(s)))))"
 (theory sequences)
 (usages transportable-macete)
 (proof
  (direct-and-antecedent-inference-strategy
   (case-split ("f_seq_q{s}"))
   (apply-macete-with-minor-premises meaning-of-length-rev)
   simplify
   simplify)))   

(def-theorem sequences-same-length-same-domain 
  "forall(s_1,s_2:[nn,ind_1], 
	f_seq_q(s_1) and f_seq_q(s_2) 
	 implies
	forall(m:nn, #(s_1(m)) iff #(s_2(m))) 
	iff
	length(s_1)=length(s_2))"
 (theory sequences)
 (usages transportable-macete)
 (proof ((apply-macete-with-minor-premises iota-free-definition-of-length)
	 (apply-macete-with-minor-premises meaning-of-length-rev)
	 direct-and-antecedent-inference-strategy-with-simplification)))

(def-theorem length-existence-implies-uniqueness 
  "forall(t:[nn,ind_1],
    forall(i:nn,
      forall(m:nn,m<i iff #(t(m)))
       implies 
      forall(j:nn,forall(m:nn,m<j iff #(t(m))) implies j=i)))"
  (theory sequences)
  (proof
   (direct-and-antecedent-inference-strategy
    (instantiate-theorem trichotomy ("i" "j"))
    (instantiate-universal-antecedent
     "with(t:[nn,ind_1],i:nn,forall(m:nn,m<i iff #(t(m))));" ("j"))
    (instantiate-universal-antecedent
     "with(t:[nn,ind_1],j:nn,forall(m:nn,m<j iff #(t(m))));" ("j"))
    simplify
    (instantiate-universal-antecedent
     "with(t:[nn,ind_1],j:nn,forall(m:nn,m<j iff #(t(m))));" ("i"))
    (instantiate-universal-antecedent
     "with(t:[nn,ind_1],i:nn,forall(m:nn,m<i iff #(t(m))));" ("i"))
    simplify)))


(def-theorem length-non-negative
  "forall(s:[nn,ind_1], f_seq_q{s} implies 0<=length{s})"
  (theory sequences)
  (usages transportable-macete)
  (proof (simplify-insistently)))

(def-theorem sequence-defined-monotonically 
  "forall(s:[nn,ind_1], m,n:nn, f_seq_q{s} and m<=n and #(s(n)) implies #(s(m)))"
 (theory sequences)
 (usages transportable-macete)
  (proof ((apply-macete-with-minor-premises sequence-defined-up-to-length)
	  (apply-macete-with-minor-premises meaning-of-length-rev)
	  direct-and-antecedent-inference-strategy
	  simplify)))

;; (!)

(def-theorem f_seq_q-characterization
  "forall(s:[nn->ind_1], 
      f_seq_q{s} 
    iff
     (forall(i,j:nn, i<j and #(s(j)) implies #(s(i)))
      and forsome(k:nn, not(#(s(k))))))"
  (theory sequences)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 0)")
      (apply-macete-with-minor-premises sequence-defined-monotonically)
      auto-instantiate-existential
      simplify)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1)")
      (instantiate-existential ("length{s}"))
      (apply-macete-with-minor-premises sequence-not-defined-at-length))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
      (contrapose "with(p:prop,not(p));")
      (cut-with-single-formula "forall(m:zz, 0<=m implies #(s(m)))")
      simplify
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(induction integer-inductor ("m"))
	(block 
	  (script-comment "`induction' at (0 0 0)")
	  (contrapose "with(p:prop,not(p));")
	  (cut-with-single-formula "length{s}=0")
	  (apply-macete-with-minor-premises iota-free-definition-of-length)
	  simplify
	  direct-inference
	  (case-split ("0<m"))
	  (auto-instantiate-universal-antecedent "with(s:[nn,ind_1],
  forall(i,j:nn,i<j and #(s(j)) implies #(s(i))));")
	  (block 
	    (script-comment "`case-split' at (2)")
	    simplify
	    (cut-with-single-formula "0=m")
	    simplify
	    simplify))
	(block 
	  (script-comment "`induction' at (0 1 0 0 0 0)")
	  (contrapose "with(p:prop,not(p));")
	  (cut-with-single-formula "length{s}=1+t")
	  (apply-macete-with-minor-premises iota-free-definition-of-length)
	  direct-and-antecedent-inference-strategy
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
	    (case-split ("m=t"))
	    simplify
	    (block 
	      (script-comment "`case-split' at (2)")
	      (instantiate-universal-antecedent "with(p:prop,forall(i,j:nn,p));"
                                                                 
						("m" "t"))
	      (contrapose "with(t:zz,m:nn,not(m<t));")
	      simplify))
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
	    (contrapose "with(p:prop,not(p));")
	    (case-split ("(m=1+t)"))
	    simplify
	    (block 
	      (script-comment "`case-split' at (2)")
	      (instantiate-universal-antecedent "with(p:prop,forall(i,j:nn,p));"
                                                                 
						("1+t" "m"))
	      (contrapose "with(m:nn,t:zz,not(1+t<m));")
	      simplify)))))))) 


;;; NIL

(transportable-rewrite-usage-simplog1st
 (def-theorem length-of-nil 
   "length(nil(ind_1)) = 0"
   (theory sequences)
   (usages transportable-macete transportable-rewrite)
   (proof (simplify-insistently
	   (eliminate-iota 0)
	   (instantiate-existential ("0"))
	   simplify
	   (instantiate-universal-antecedent
	    "with(z%iota:nn,forall(m_$0:nn,not(m_$0<z%iota)));" ("0"))
	   simplify))))

(transportable-rewrite-usage-simplog1st
 (def-theorem length-0-iff-nil 	
   "forall(s:[nn,ind_1], length(s) = 0 iff s=nil(ind_1))"
   reverse
   (theory sequences)
   (usages transportable-macete transportable-rewrite)
   (proof ((apply-macete-with-minor-premises iota-free-definition-of-length)
	   simplify
	   direct-and-antecedent-inference-strategy
	   extensionality
	   simplify
	   simplify
	   ))))

(def-theorem length-0-implies-nil 				
  "forall(s:[nn,ind_1], length(s) = 0 implies s=nil(ind_1))"
  (theory sequences)
  (usages transportable-macete)
    (proof ((apply-macete-with-minor-premises length-0-iff-nil))))

(def-theorem nil-is-fseq
  "f_seq_q(nil(ind_1))"
  (theory sequences)
  (usages transportable-macete)
  (proof ((assume-theorem length-0-iff-nil)
	  simplify)))

(def-theorem non-nil-fseq-defined-at-0
  "forall(s:[nn,ind_1], f_seq_q(s) and not(s=nil{ind_1}) implies #(s(0)))"
 (theory sequences)
 (usages transportable-macete)
 (proof ((apply-macete-with-minor-premises meaning-of-length-rev)
	 direct-and-antecedent-inference-strategy
	 (instantiate-theorem length-0-implies-nil ("s"))
	 simplify)))

;;; CONS

(transportable-rewrite-usage-simplog1st
 (def-theorem car-of-cons 
   "forall([[[x],ind_1],[[s],[nn,ind_1]]], cons(x,s)(0) = x)"
   (theory sequences)
   (usages transportable-macete transportable-rewrite)
   (proof (simplify))))

(transportable-rewrite-usage-simplog1st
 (def-theorem cdr-of-cons 
   "forall([[[x],ind_1],[[s],[nn,ind_1]]], drop(cons(x,s),1) = s)"
   (theory sequences)
   (usages transportable-macete transportable-rewrite)
   (proof (simplify-insistently
	   (apply-macete-with-minor-premises tr%unary-eta-reduction)))))

;; (!) 

(def-theorem length-of-cons 
  "forall(x:ind_1,s:[nn,ind_1],
     f_seq_q{s} implies length{cons{x,s}}=length{s}+1)"
  (theory sequences)
  (usages transportable-macete)
  (proof
   (


    (apply-macete-with-minor-premises iota-free-definition-of-length)
    simplify
    (apply-macete-with-minor-premises meaning-of-length-rev)
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "0<=length{s}")
    simplify
    (apply-macete-with-minor-premises length-non-negative)
    )))

(comment
 ;; with alternate simplifiers 
 (proof
  (
   (apply-macete-with-minor-premises iota-free-definition-of-length)
   simplify
   (apply-macete-with-minor-premises meaning-of-length-rev)
   (command-on-direct-descendents simplify))))

(def-theorem cons-is-fseq
  "forall(x:ind_1,s:[nn,ind_1],
     f_seq_q{s} implies f_seq_q{cons{x,s}})"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  (instantiate-theorem length-of-cons ("x" "s")))))


;; (!)

(def-theorem length-of-pre-cons
  "forall(x:ind_1,s:[nn,ind_1],
     f_seq_q{cons{x,s}} implies length{s}=length{cons{x,s}}-1)"
  (theory sequences)
  (usages transportable-macete)
  (proof
   ((apply-macete-with-minor-premises iota-free-definition-of-length)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(s:[nn,ind_1],x:ind_1,m:nn,m<length{cons{x,s}}-1);")
    simplify
    (apply-macete-with-minor-premises length-characterizes-definedness)
    simplify
    simplify
    (apply-macete-with-minor-premises meaning-of-length)
    (cut-with-single-formula "0<length{cons{x,s}}")
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    (apply-macete-with-minor-premises meaning-of-length)
    simplify)))


(def-theorem cons-fseq-implies-fseq
  "forall(x:ind_1,s:[nn,ind_1],
     f_seq_q{cons{x,s}} implies f_seq_q{s})"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  (instantiate-theorem length-of-pre-cons ("x" "s")))))

(transportable-rewrite-usage-simplog1st
 (def-theorem length-of-cons-rew 				; proof (no history)
   "forall(x:ind_1,s:[nn,ind_1],length{cons{x,s}}==length{s}+1)"
  (theory sequences)
  (usages transportable-rewrite)
  (proof (insistent-direct-inference-strategy
	  (antecedent-inference
	   "with(s:[nn,ind_1],x:ind_1, f_seq_q{cons{x,s}} or #(length{s}+1));")
	  (instantiate-theorem length-of-pre-cons ("x" "s"))
	  simplify
	  (apply-macete-with-minor-premises length-of-cons)))))

(def-theorem length-of-cons-alt-1
  "forall(s:[nn,ind_1],x:ind_1, 
 	f_seq_q{cons{x,s}} 
 	 implies
	length{s}=length{cons{x,s}}-1);"
  (theory sequences)
  (usages )
  (proof ((apply-macete-with-minor-premises length-of-pre-cons)
	  simplify
	  (apply-macete-with-minor-premises cons-fseq-implies-fseq))))

(def-theorem length-of-cons-alt	
  "forall(x:ind_1,s:[nn,ind_1],
  f_seq_q{cons{x,s}} implies length{cons{x,s}}=length{s}+1)"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  (instantiate-theorem length-of-pre-cons ("x" "s"))
	  simplify)))

(transportable-rewrite-usage-simplog1st
 (def-theorem cons-fseq-biconditional 
   "forall(x:ind_1,s:[nn,ind_1],
  f_seq_q{cons{x,s}} iff f_seq_q{s});"
   (theory sequences)
   (usages transportable-macete transportable-rewrite)
   (proof (direct-and-antecedent-inference-strategy
	   (apply-macete-with-minor-premises cons-fseq-implies-fseq)
	   auto-instantiate-existential
	   (apply-macete-with-minor-premises cons-is-fseq)))))


(def-theorem cons-to-nil-is-fseq
  "forall(e:ind_1,f_seq_q{cons{e,nil{ind_1}}})"
  (theory sequences)
  (usages transportable-macete)
  (proof ((apply-macete-with-minor-premises cons-is-fseq)
	  (apply-macete-with-minor-premises nil-is-fseq))))

;; (transportable-rewrite-usage-simplog1st
;; (def-theorem cons-non-nil 
;;    "forall(e:ind_1, s:[nn,ind_1], cons(e,s)=nil(ind_1) iff falsehood)"
;;   (theory sequences)
;;   (usages transportable-rewrite)
;;   (proof "$GENERIC_THEORIES/proofs/sequences.cons-non-nil.t")))

(transportable-rewrite-usage-simplog1st
 (def-theorem cons-non-nil-2
   "forall(e:ind_1,s:[nn,ind_1], not(cons(e,s)=nil{ind_1}))"
   (theory sequences)
   (usages transportable-rewrite transportable-macete)
   (proof (direct-and-antecedent-inference-strategy
	   extensionality
	   (instantiate-existential ("0"))
	   simplify))))

;;; TAKEFIRST

(transportable-rewrite-usage-simplog1st
 (def-theorem take-none
   "forall(s:[nn,ind_1], takefirst(s,0) = nil(ind_1))"
   (theory sequences)
   (usages transportable-macete transportable-rewrite)
   (proof (direct-and-antecedent-inference-strategy
	   extensionality
	   simplify))))

(def-theorem take-all
  "forall(s:[nn,ind_1], f_seq_q(s) implies 
             takefirst(s,length(s)) = s)"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  extensionality
	  simplify
	  direct-and-antecedent-inference-strategy
	  (case-split-on-conditionals (0))
	  (apply-macete-with-minor-premises meaning-of-length-rev))))

;; (!)

(def-theorem length-of-takefirst 
  "forall(s:[nn,ind_1],k:nn, f_seq_q(s) implies
             length(takefirst(s,k)) = if(k<=length(s),k,length(s)))"
 (theory sequences)
 (usages transportable-macete)
 (proof (direct-and-antecedent-inference-strategy
	 (case-split-on-conditionals (0))
	 (apply-macete-with-minor-premises iota-free-definition-of-length)
	 simplify
	 direct-and-antecedent-inference-strategy
	 (apply-macete-with-minor-premises sequence-defined-up-to-length)
	 simplify
	 (apply-macete-with-minor-premises iota-free-definition-of-length)
	 simplify
	 direct-and-antecedent-inference-strategy
	 simplify
	 (apply-macete-with-minor-premises sequence-defined-up-to-length)
	 (apply-macete-with-minor-premises length-characterizes-definedness))))

(def-theorem takefirst-is-fseq
  "forall(s:[nn,ind_1],k:nn, f_seq_q(s) implies
               f_seq_q(takefirst(s,k)))"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  (instantiate-theorem length-of-takefirst ("s" "k")))))

;;; DROP

(transportable-rewrite-usage-simplog1st
 (def-theorem drop-none
   "forall(s:[nn,ind_1], drop(s,0) = s)"
  (theory sequences)
  (usages transportable-macete transportable-rewrite)
  (proof (simplify-insistently
	  (apply-macete-with-minor-premises tr%unary-eta-reduction)))))

(def-theorem drop-all-or-more
  "forall([[[m],nn],[[s],[nn,ind_1]]], (f_seq_q(s) and length(s)<=m) implies 
             drop(s,m) = nil(ind_1))"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  extensionality
	  simplify
	  (apply-macete-with-minor-premises meaning-of-length-rev)
	  simplify)))

(def-theorem drop-all
  "forall(s:[nn,ind_1],
    f_seq_q{s} implies drop{s,length{s}}=nil{ind_1})"
  (theory sequences)
  (usages transportable-macete)
  (proof ((apply-macete-with-minor-premises drop-all-or-more)
	  direct-and-antecedent-inference-strategy)))

;; (!)

(def-theorem length-of-drop
  "forall(s:[nn,ind_1],k:nn,
  f_seq_q{s}
   implies 
  length{drop{s,k}}=if(k<=length{s}, length{s}-k, 0));"
 (theory sequences)
 (usages transportable-macete)
 (proof
  (direct-and-antecedent-inference-strategy
   (case-split-on-conditionals (0))
   (force-substitution "k+length{drop{s,k}}=length{s}" "length{drop{s,k}}=length{s}-k" (0))
   (apply-macete-with-minor-premises iota-free-definition-of-length)
   simplify
   (apply-macete-with-minor-premises length-characterizes-definedness)
   direct-inference
   simplify
   (apply-macete-with-minor-premises drop-all-or-more)
   (apply-macete-with-minor-premises length-of-nil))))

(def-theorem drop-is-fseq 
  "forall(s:[nn,ind_1],k:nn,
  f_seq_q{s} implies f_seq_q{drop{s,k}})"
 (theory sequences)
 (usages transportable-macete)
 (proof (direct-and-antecedent-inference-strategy
	 (instantiate-theorem length-of-drop ("s" "k")))))


(def-theorem cons-car-cdr-lemma
  "forall(s:[nn,ind_1], #(s(0)) implies cons{s(0),drop{s,1}}=s)"
  (theory sequences)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    extensionality
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (case-split-on-conditionals (0))
    (cut-with-single-formula "x_0=0")
    simplify
    )))


(def-theorem cons-car-cdr 
  "forall(s:[nn,ind_1], 
 	1<=length(s) 
 	 implies
	cons(s(0),drop(s,1))=s)"
  (theory sequences)
  (usages transportable-macete)
  (proof
   (
	  

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises cons-car-cdr-lemma)
    (apply-macete-with-minor-premises sequence-defined-up-to-length)
    simplify
    )))

(def-theorem existential-cons-car-cdr
  "forall(s:[nn,ind_1], 0<length{s} 
	implies
	 forsome(i:ind_1, s_1:[nn,ind_1], s=cons(i,s_1)))"
  (theory sequences)
  (usages )
  (proof (direct-and-antecedent-inference-strategy
	  (instantiate-existential ("s(0)" "drop{s,1}"))
	  (apply-macete-with-minor-premises cons-car-cdr)
	  (apply-macete-with-minor-premises sequence-defined-up-to-length))))

(def-theorem drop-cons 
  "forall(s:[nn,ind_1], n:nn, e:ind_1,
      1<=n implies 
	drop{cons(e,s),n}=drop{s,n-1})"
 (theory sequences)
 (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  extensionality
	  direct-and-antecedent-inference-strategy
	  simplify
	  (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
	  simplify)))

(def-compound-macete drop-cons-and-simplify 
  (series
   (repeat (without-minor-premises tr%drop-cons))
   simplify))

(def-theorem drop-from-nil
  "forall(n:nn, drop{nil{ind_1},n}=nil{ind_1})"
  (theory sequences)
  (usages transportable-macete transportable-rewrite)
  (proof ((apply-macete-with-minor-premises drop-all-or-more)
	  (apply-macete-with-minor-premises length-of-nil)
	  simplify
	  simplify)))


;;; APPEND

(def-theorem takefirst-of-cons
  "forall(a:ind_1, s:[nn,ind_1], n:nn, 
     0<n implies takefirst{cons{a,s},n} = cons{a,takefirst{s,n-1}})"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  extensionality
	  simplify-with-minor-premises
	  direct-inference
	  (case-split-on-conditionals (1))
	  (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
	  simplify)))

(def-theorem takefirst-of-append-at-length 
  "forall(s,t:[nn,ind_1], f_seq_q(s) implies 
             takefirst(append(s,t),length(s)) = s)"
  (theory sequences)
  (usages transportable-macete)
  (proof (
	  direct-and-antecedent-inference-strategy
	  extensionality
	  simplify
	  direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises meaning-of-length-rev)
	  )))

;; (!)

(def-theorem takefirst-of-append
  "forall(s,t:[nn,ind_1], n:nn, length{s}<n implies 
             takefirst{append{s,t},n} = append{s,takefirst{t,n-length{s}}})"
  (theory sequences)
  (usages transportable-macete)
  (proof (
	  direct-and-antecedent-inference-strategy
	  extensionality
	  simplify
	  direct-and-antecedent-inference-strategy
	  (case-split-on-conditionals (0))
	  (case-split-on-conditionals (0))
	  insistent-direct-and-antecedent-inference-strategy
	  simplify
	  simplify)))


(comment
 (proof
  (
   (prove-by-logic-and-simplification 0))))


(def-theorem drop-of-append
  "forall(s,t:[nn,ind_1],
  f_seq_q{s} implies drop{append{s,t},length{s}}=t)"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  extensionality
	  simplify)))

(def-theorem drop-some-from-append 					
  "forall(s_0,s_1:[nn,ind_1], m:nn, 
         m<=length{s_0}
      implies
         drop{append{s_0,s_1},m}=append{drop{s_0,m},s_1})"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  extensionality
	  simplify
	  direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises length-of-drop)
	  simplify)))

;; (!)

(def-theorem length-of-append 
  "forall(s,t:[nn,ind_1],
  f_seq_q{s} and f_seq_q{t}
   implies 
  length{append{s,t}}=length{s}+length{t})"
 (theory sequences)
 (usages transportable-macete)
  (proof
   ((apply-macete-with-minor-premises iota-free-definition-of-length)
    simplify
    direct-and-antecedent-inference-strategy
    (case-split-on-conditionals (0))
    (apply-macete-with-minor-premises sequence-defined-up-to-length)
    simplify
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    (apply-macete-with-minor-premises sequence-defined-up-to-length)
    simplify
    (incorporate-antecedent
     "with(t:[nn,ind_1],m:nn,s:[nn,ind_1], 
     #(if(length{s}<=m, t(m+[-1]*length{s}), s(m))));")
    (case-split-on-conditionals (0))
    (apply-macete-with-minor-premises meaning-of-length-rev)
    simplify
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify)))


(comment
 (proof
  (
   (apply-macete-with-minor-premises iota-free-definition-of-length)
   simplify
   (raise-conditional (0))
   (apply-macete-with-minor-premises meaning-of-length-rev)
   (command-on-direct-descendents simplify))))

(def-theorem infinite-append 
  "forall(s,t:[nn,ind_1],not(f_seq_q{s}) implies append{s,t}=s)"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  extensionality
	  simplify
	  direct-and-antecedent-inference-strategy
	  (cut-with-single-formula "not(length{s}<=x_0)")
	  simplify
	  simplify)))

(comment
 ;; -- with either simplifier version
 (proof
  (
   (prove-by-logic-and-simplification 0))))
	 

(def-theorem append-is-fseq 
  "forall(s,t:[nn,ind_1],
  f_seq_q{s} and f_seq_q{t} implies f_seq_q{append{s,t}})"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  (instantiate-theorem length-of-append ("s" "t")))))

(def-theorem append-shifts-second-arg 
  "forall(s,t:[nn,ind_1], 
    #(length(s)) 
    implies
   forall(m:nn, 
    length(s)<=m 
    implies
   append(s,t)(m)==t(m-length(s))))"
  (theory sequences)
  (proof (simplify)))
     
(def-theorem append-fseq-implies-first-fseq
  "forall(s,t:[nn,ind_1],
  f_seq_q{append{s,t}} implies f_seq_q{s})"
  (theory sequences)
  (proof (direct-and-antecedent-inference-strategy
	  (contrapose "with(t,s:[nn,ind_1],f_seq_q{append{s,t}});")
	  (apply-macete-with-minor-premises infinite-append)
	  )))

(def-theorem append-fseq-implies-second-fseq 
  "forall(s,t:[nn,ind_1],
  f_seq_q{append{s,t}} implies f_seq_q{t})"
  (theory sequences)
  (proof (direct-and-antecedent-inference-strategy
	  (force-substitution "t" "drop{append{s,t},length{s}}" (0))
	  (apply-macete-with-minor-premises drop-is-fseq)
	  (apply-macete-with-minor-premises append-fseq-implies-first-fseq)
	  auto-instantiate-existential
	  (apply-macete-with-minor-premises drop-of-append))))

(def-theorem append-fseq-macete				; ;;  short proof
  "forall(s,t:[nn,ind_1],
  f_seq_q{append{s,t}} iff (f_seq_q{s} and f_seq_q{t}))"
  (theory sequences)
  (usages transportable-macete transportable-rewrite)
  (proof (direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises append-fseq-implies-first-fseq)
	  auto-instantiate-existential
	  (apply-macete-with-minor-premises append-fseq-implies-second-fseq)
	  auto-instantiate-existential
	  (apply-macete-with-minor-premises append-is-fseq)
	  simplify)))
 
;; (def-theorem append-is-fseq-rewrite 
;;   "forall(s_0,s_1:[nn,ind_1],
;; 	 f_seq_q{append{s_0,s_1}} iff (f_seq_q{s_0} and f_seq_q{s_1}))"
;;  (theory sequences)
;;  (usages transportable-macete transportable-rewrite))

(def-theorem length-of-append-quasi-eq 
  "forall(x,y:[nn,ind_1], 
 	length{append{x,y}}==length{x}+length{y})"
  (theory sequences)
  (usages transportable-macete)
  (proof (insistent-direct-inference-strategy
	  (antecedent-inference "with(y,x:[nn,ind_1],
  f_seq_q{append{x,y}} or #(length{x}+length{y}));")
	  (apply-macete-with-minor-premises length-of-append)
	  simplify
	  (instantiate-theorem append-fseq-macete ("x" "y"))
	  (apply-macete-with-minor-premises append-fseq-implies-second-fseq)
	  auto-instantiate-existential
	  (apply-macete-with-minor-premises append-fseq-implies-first-fseq)
	  auto-instantiate-existential
	  (apply-macete-with-minor-premises length-of-append))))

(transportable-rewrite-usage-simplog1st
 (def-theorem append-nil 				;  proof ( history)
   "forall(s:[nn,ind_1], append(nil(ind_1),s)=s)"
   (theory sequences)
   (usages transportable-macete transportable-rewrite)
   (proof (direct-and-antecedent-inference-strategy
	   extensionality
	   simplify
	   (apply-macete-with-minor-premises length-of-nil)
	   simplify))))

(transportable-rewrite-usage-simplog1st
 (def-theorem append-nil-right 	
   "forall(s:[nn,ind_1], append(s,nil(ind_1))=s)"
   (theory sequences)
   (usages transportable-macete transportable-rewrite)
   (proof (direct-and-antecedent-inference-strategy
	   extensionality
	   simplify
	   direct-and-antecedent-inference-strategy
	   (case-split-on-conditionals (0))
	   (apply-macete-with-minor-premises meaning-of-length-rev)
	   simplify))))

;; (!)

(def-theorem append-is-nil-implies-left-is-nil		;  proof ( history)
  "forall(s_0,s_1:[nn,ind_1], append(s_0,s_1)=nil(ind_1) implies s_0=nil(ind_1))"
  (theory sequences)
  (usages transportable-macete)
  (proof
   ((force-substitution "s_0=nil{ind_1}" "length{s_0}=0" (0))
    (force-substitution "append{s_0,s_1}=nil{ind_1}" "length{append{s_0,s_1}}=0" (0))
    direct-and-antecedent-inference-strategy
    (case-split ("f_seq_q{append{s_0,s_1}}"))
    (cut-with-single-formula "length{s_0}<=length{append{s_0,s_1}}")
    simplify
    (apply-macete-with-minor-premises length-of-append)
    (instantiate-theorem length-non-negative ("s_1"))
    (contrapose "with(s_1:[nn,ind_1],not(f_seq_q{s_1}));")
    (weaken (0 2))
    (apply-macete-with-minor-premises append-fseq-implies-second-fseq)
    auto-instantiate-existential
    simplify
    (weaken (0 2))
    (apply-macete-with-minor-premises append-fseq-implies-first-fseq)
    auto-instantiate-existential
    (weaken (1))
    (weaken (1))
    (apply-macete-with-minor-premises length-0-iff-nil)
    (apply-macete-with-minor-premises length-0-iff-nil))))
  
(comment
 (proof
  (

   (force-substitution-then-justify "s_0=nil{ind_1}" "length{s_0}=0")

   )))



(transportable-rewrite-usage-simplog1st
 (def-theorem append-cons-fseq 				
   "forall(t,u:[nn,ind_1],e:ind_1, 
     f_seq_q{t} implies
     append{cons{e,t},u}=cons{e,append{t,u}})"
   (theory sequences)
   (usages )
   (proof
    (


     direct-and-antecedent-inference-strategy
     extensionality
     direct-and-antecedent-inference-strategy
     simplify
     direct-and-antecedent-inference-strategy
     (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
       (case-split-on-conditionals (0))
       (incorporate-antecedent "with(x_0,n:nn,n<=x_0);")
       (apply-macete-with-minor-premises length-of-cons)
       (cut-with-single-formula "0<=length{t}")
       (move-to-sibling 1)
       (apply-macete-with-minor-premises length-non-negative)
       simplify)
     (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
       (apply-macete-with-minor-premises length-of-cons)
       simplify)
     ))))

(def-theorem append-cons-not-fseq 				
  "forall(t,u:[nn,ind_1],e:ind_1, 
     not(f_seq_q{t}) 
      implies
     append{cons{e,t},u}=cons{e,append{t,u}})"
  (theory sequences)
  (usages )
  (proof ((apply-macete-with-minor-premises infinite-append)
	  (apply-macete-with-minor-premises cons-fseq-biconditional))))

(def-theorem append-cons 				
  "forall(t,u:[nn,ind_1],e:ind_1, 
 append{cons{e,t},u}=cons{e,append{t,u}})"
  (theory sequences)
  (usages transportable-macete transportable-rewrite)
  (proof (direct-and-antecedent-inference-strategy
	  (case-split ("f_seq_q{t}"))
	  (apply-macete-with-minor-premises append-cons-fseq)
	  (apply-macete-with-minor-premises append-cons-not-fseq)
	  )))

(def-theorem cons-append 				
  "forall(t,u:[nn,ind_1],e:ind_1, 
 cons{e,append{t,u}}=append{cons{e,t},u})"
  (theory sequences)
  (usages transportable-macete)
  (proof ((apply-macete-with-minor-premises append-cons))))

(def-theorem last-of-append-single
  "forall(s:[nn,ind_1],s_f:ind_1,
  f_seq_q{s}
   implies 
  append{s,seq{s_f,ind_1}}(length{append{s,seq{s_f,ind_1}}}-1)=s_f)"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises length-of-append)
	  (apply-macete-with-minor-premises length-of-cons)
	  (apply-macete-with-minor-premises length-of-nil)
	  (apply-macete-with-minor-premises append-shifts-second-arg)
	  simplify
	  (apply-macete-with-minor-premises nil-is-fseq)
	  (apply-macete-with-minor-premises nil-is-fseq)
	  (apply-macete-with-minor-premises cons-to-nil-is-fseq))))

(def-theorem append-agrees-with-first-below-length
  "forall(s_0,s_1:[nn,ind_1],i:nn, i<length{s_0} implies append{s_0,s_1}(i)=s_0(i))"
  (theory sequences)
  (usages transportable-macete)
  (proof (beta-reduce-with-minor-premises
	  simplify
	  (apply-macete-with-minor-premises sequence-defined-up-to-length))))
 
(def-theorem sequence-induction 				
  "forall(p:[[nn,ind_1],prop],
	forall(s:[nn,ind_1],
	 f_seq_q(s) implies p(s))
      iff
	(p(nil(ind_1))
	and 
	 forall(s:[nn,ind_1], e:ind_1,
	  f_seq_q(s) and p(s) implies p(cons{e,s}))))"
  (theory sequences)
  (usages transportable-macete)
  (proof
   (direct-inference
    direct-inference
    direct-and-antecedent-inference-strategy
    (backchain "with(p:[[nn,ind_1],prop],
  forall(s:[nn,ind_1],f_seq_q{s} implies p(s)));")
    (apply-macete-with-minor-premises nil-is-fseq)
    (backchain "with(p:[[nn,ind_1],prop],
  forall(s:[nn,ind_1],f_seq_q{s} implies p(s)));")
    (apply-macete-with-minor-premises cons-is-fseq)
    (cut-with-single-formula "forall(j:zz, 0<=j implies forall(s:[nn,ind_1], length{s}<=j implies p(s)))")
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:[[nn,ind_1],prop],
  forall(j:zz,
    0<=j
     implies 
    forall(s:[nn,ind_1],length{s}<=j implies p(s))));" ("length{s}"))
    (contrapose "with(s:[nn,ind_1],not(0<=length{s}));")
    (apply-macete-with-minor-premises length-non-negative)
    (instantiate-universal-antecedent "with(p:[[nn,ind_1],prop],s:[nn,ind_1],
  forall(s_$0:[nn,ind_1],
    length{s_$0}<=length{s} implies p(s_$0)));" ("s"))
    (contrapose "with(s:[nn,ind_1],not(length{s}<=length{s}));")
    simplify
    (induction integer-inductor ("j"))
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "s=nil{ind_1}")
    simplify
    (instantiate-theorem length-non-negative ("s"))
    (instantiate-theorem length-0-implies-nil ("s"))
    (contrapose "with(s:[nn,ind_1],not(length{s}=0));")
    simplify
    (case-split ("length{s}=1+t"))
    (instantiate-theorem existential-cons-car-cdr ("s"))
    (contrapose "with(s:[nn,ind_1],not(0<length{s}));")
    simplify
    (cut-with-single-formula "length{s_1}=t")
    (instantiate-universal-antecedent "with(p:[[nn,ind_1],prop],t:zz,
  forall(s:[nn,ind_1],length{s}<=t implies p(s)));" ("s_1"))
    (contrapose "with(t:zz,s_1:[nn,ind_1],not(length{s_1}<=t));")
    simplify
    (backchain "with(s_1:[nn,ind_1],i:ind_1,s:[nn,ind_1],s=cons{i,s_1});")
    (backchain "with(p:[[nn,ind_1],prop],
  forall(s:[nn,ind_1],e:ind_1,
    f_seq_q{s} and p(s) implies p(cons{e,s})));")
    simplify
    (incorporate-antecedent "with(t:zz,s:[nn,ind_1],length{s}=1+t);")
    (backchain "with(s_1:[nn,ind_1],i:ind_1,s:[nn,ind_1],s=cons{i,s_1});")
    (apply-macete-with-minor-premises length-of-cons)
    simplify
    (apply-macete-with-minor-premises cons-fseq-implies-fseq)
    (instantiate-existential ("i"))
    simplify
    (backchain "with(p:[[nn,ind_1],prop],t:zz,  forall(s:[nn,ind_1],length{s}<=t implies p(s)));")
    simplify)))

(def-inductor sequence-inductor
  sequence-induction
  (theory sequences)
  (base-case-hook simplify))


(transportable-rewrite-usage-simplog1st
 (def-theorem associativity-of-append 
   "forall(s,t,u:[nn,ind_1],
  append{append{s,t},u}=append{s,append{t,u}})"
   (theory sequences)
   (usages transportable-macete transportable-rewrite)
   (proof (direct-and-antecedent-inference-strategy
	   (case-split ("f_seq_q{s}"))
	   (block (script-comment "Main case: first arg is finite.")
		  (let-macete
		   append-macete
		   (series (repeat append-nil append-cons) simplify))
		  (label-node main-case)
		  (induction sequence-inductor ())
		  (jump-to-node main-case)
		  (for-nodes
		   (unsupported-descendents)
		   (apply-macete-with-minor-premises $append-macete)))
	   (block (script-comment "Supplementary case: first arg infinite.")
		  (let-macete inf-app-repeat
			      (repeat infinite-append))
		  (apply-macete-with-minor-premises $inf-app-repeat)
		  (contrapose "with(s:[nn,ind_1],not(f_seq_q{s}));")
		  (apply-macete-with-minor-premises append-fseq-implies-first-fseq)
		  auto-instantiate-existential)))))

(def-theorem sequence-cases 				
  "forall(s:[nn,ind_1],
       f_seq_q{s} 
	implies
       (s=nil{ind_1}
	 or
	forsome(x:ind_1, s_0:[nn,ind_1], s=cons{x,s_0} and  f_seq_q{s_0}))) "
  (theory sequences)
  (usages transportable-macete)
  (proof ((induction sequence-inductor ("s"))
	  direct-and-antecedent-inference-strategy
	  (instantiate-existential ("s"))
	  (instantiate-existential ("e")))))


(def-theorem sequence-cases-on-right
  "forall(s:[nn,ind_1], s=nil{ind_1} or 
      forsome(e:ind_1, s_1:[nn,ind_1], s=append{s_1,cons{e,nil{ind_1}}}))"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  (case-split ("f_seq_q{s}"))
	  (induction sequence-inductor ("s"))
	  (antecedent-inference "with(s:[nn,ind_1],
  not(s=nil{ind_1})
   implies 
  forsome(e:ind_1,s_1:[nn,ind_1],
    s=append{s_1,seq{e,ind_1}}));")
	  (instantiate-existential ("e" "nil{ind_1}"))
	  (apply-macete-with-minor-premises append-nil)
	  (backchain "with(s:[nn,ind_1],s=nil{ind_1});")
	  (antecedent-inference "with(s:[nn,ind_1],
  forsome(e:ind_1,s_1:[nn,ind_1],
    s=append{s_1,seq{e,ind_1}}));")
	  (instantiate-existential ("e_$0" "cons{e,s_1}"))
	  (backchain "with(e_$0:ind_1,s_1,s:[nn,ind_1],
  s=append{s_1,seq{e_$0,ind_1}});")
	  (apply-macete-with-minor-premises append-cons)
	  (instantiate-existential ("e" "s"))
	  (apply-macete-with-minor-premises infinite-append))))

(def-theorem sequence-decomposition-on-right
  "forall(s:[nn,ind_1], 0<length{s} implies
      forsome(e:ind_1, s_1:[nn,ind_1], s=append{s_1,cons{e,nil{ind_1}}}))"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  (instantiate-theorem sequence-cases-on-right ("s"))
	  (contrapose "with(n:nn,0<n);")
	  (backchain "with(f,s:[nn,ind_1],s=f);")
	  (apply-macete-with-minor-premises length-of-nil)
	  simplify)))

(def-theorem sequence-induction-on-right 				
  "forall(p:[[nn,ind_1],prop],
	forall(s:[nn,ind_1],
	 f_seq_q(s) implies p(s))
      iff
	(p(nil(ind_1))
	and 
	 forall(s:[nn,ind_1], e:ind_1,
	  f_seq_q(s) and p(s) implies p(append{s,cons{e,nil{ind_1}}}))))"
  (theory sequences)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    direct-inference
    (block (script-comment "First prove easy direction: =>")
	   direct-and-antecedent-inference-strategy 
	   (backchain "with(p:prop,p);")
	   (apply-macete-with-minor-premises nil-is-fseq)
	   (backchain "with(p:prop,forall(s:[nn,ind_1],p));")
	   (apply-macete-with-minor-premises append-is-fseq)
	   (apply-macete-with-minor-premises cons-to-nil-is-fseq))
    (block (script-comment "Next prove other direction: =>.  
	Requires induction on length.")
	   (cut-with-single-formula "forall(j:zz, 0<=j implies forall(s:[nn,ind_1], length(s)=j implies p(s)))")
	   (instantiate-universal-antecedent "with(p:prop,forall(j:zz,p));"
					     ("length{s}"))
	   (block (script-comment "Observe that (0<=length{s}).")
		  (contrapose "with(p:prop,not(p));")
		  simplify)
	   (block (script-comment "Consider s_$0=s.")
		  (instantiate-universal-antecedent
		   "with(p:prop,forall(s_$0:[nn,ind_1],p));" ("s"))
		  (contrapose "with(p:prop,not(p));"))
	   (script-comment "Now prove the induction formula.")
	   (induction integer-inductor ("j"))
	   (block (script-comment "Base case.")
		  (apply-macete-with-minor-premises length-0-iff-nil)
		  simplify)
	   (block (script-comment "Induction step: decompose seq on right.")
		  (instantiate-theorem sequence-cases-on-right ("s"))
		  simplify
		  (backchain "with(f,s:[nn,ind_1],s=f);")
		  (backchain "with(p:prop,forall(s:[nn,ind_1],e:ind_1,p));")
		  (apply-macete-with-minor-premises append-fseq-implies-first-fseq)
		  direct-inference
		  (instantiate-existential ("seq{e,ind_1}"))
		  simplify
		  (backchain "with(p:prop,forall(s:[nn,ind_1],p));")
		  (cut-with-single-formula "f_seq_q{s} and f_seq_q{s_1}")
		  (contrapose "with(r:rr,n:nn,n=r);")
		  (backchain "with(f,s:[nn,ind_1],s=f);")
		  (let-macete fseq-macetes
			      (series
			       (repeat length-of-append length-of-cons length-of-nil
				       nil-is-fseq cons-to-nil-is-fseq )
			       simplify
			       append-fseq-implies-first-fseq
			       simplify))
		  (while (progresses?
			  (block (jump-to-node induction-step )
				 (for-nodes
				  (unsupported-descendents)
				  (apply-macete-with-minor-premises $fseq-macetes))))
			 (skip)))))))

(def-inductor sequence-right-inductor
  sequence-induction-on-right
  (theory sequences)
  (base-case-hook simplify))

(def-theorem in_seq-car
  "forall(x:ind_1, s:[nn,ind_1], in_seq{x, cons{x,s}})"
  (theory sequences)
  (usages transportable-macete transportable-rewrite)
  (proof (direct-and-antecedent-inference-strategy
	  (instantiate-existential ("0"))
	  simplify)))

(def-theorem in_seq-cdr
  "forall(x,y:ind_1, s:[nn,ind_1], not(x=y)
	 implies (in_seq{x, cons{y,s}} iff in_seq{x,s}))"
  (theory sequences)
  (usages transportable-macete)
  (proof (simplify-insistently
	  direct-and-antecedent-inference-strategy
	  (case-split ("i<1"))
	  (incorporate-antecedent "with(x:ind_1,s:[nn,ind_1],y:ind_1,i:nn,
  if(i<1, y, s([-1]+i))=x);")
	  simplify
	  (incorporate-antecedent "with(x:ind_1,s:[nn,ind_1],y:ind_1,i:nn,
  if(i<1, y, s([-1]+i))=x);")
	  simplify
	  direct-and-antecedent-inference-strategy
	  (instantiate-existential ("[-1]+i"))
	  (instantiate-existential ("i+1"))
	  simplify)))

(def-theorem in_seq-nil
  "forall(x:ind_1, not(in_seq{x,nil{ind_1}}))"
  (theory sequences)
  (usages transportable-rewrite transportable-macete)
  (proof (simplify-insistently)))

(def-compound-macete in_seq-macete
  (series
   (repeat
    tr%in_seq-nil
    tr%in_seq-car
    tr%in_seq-cdr)
   simplify))

(def-compound-macete sequence-length
  (series 
   (repeat tr%length-of-nil
	   tr%length-of-cons
	   tr%length-of-append
	   tr%length-of-drop
	   tr%length-of-takefirst)
   simplify))
  


;; Name chosen to honour Richard Bird, who prefers this form of sequence
;; induction in his Theory of Lists.  

(def-theorem sequence-bird-induction 
  "forall(p:[[nn,ind_1],prop],
  forall(s:[nn,ind_1],f_seq_q{s} implies p(s))
   iff 
  ((p(nil{ind_1})
   and 
  forall(e:ind_1,p(seq{e,ind_1})))
   and 
  forall(s_0,s_1:[nn,ind_1],
    f_seq_q{s_0} and f_seq_q{s_1} and p(s_0) and p(s_1)
     implies 
    p(append{s_0,s_1}))))"
  (theory sequences)
  (usages transportable-macete)
  (proof (direct-and-antecedent-inference-strategy
	  (backchain "with(p:[[nn,ind_1],prop],
  forall(s:[nn,ind_1],f_seq_q{s} implies p(s)));")
	  (apply-macete-with-minor-premises nil-is-fseq)
	  (backchain "with(p:[[nn,ind_1],prop],
  forall(s:[nn,ind_1],f_seq_q{s} implies p(s)));")
	  (apply-macete-with-minor-premises cons-to-nil-is-fseq)
	  (backchain "with(p:[[nn,ind_1],prop],
  forall(s:[nn,ind_1],f_seq_q{s} implies p(s)));")
	  (apply-macete-with-minor-premises append-is-fseq)
	  simplify
	  (induction sequence-right-inductor ("s"))
	  (backchain "with(p:[[nn,ind_1],prop],
  forall(s_0,s_1:[nn,ind_1],
    f_seq_q{s_0} and f_seq_q{s_1} and p(s_0) and p(s_1)
     implies 
    p(append{s_0,s_1})));")
	  simplify
	  (apply-macete-with-minor-premises cons-to-nil-is-fseq))))


(def-inductor sequence-bird-inductor
  sequence-bird-induction
  (theory sequences)
  (base-case-hook simplify))

(def-imported-rewrite-rules h-o-real-arithmetic
  (source-theories sequences))


