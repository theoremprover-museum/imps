(herald def-form-builder)

(*require nil '(imps /resources/lisp-supplements) standard-env)

(include-files
  (files (imps theories/networks/networks)))

(define (build-renamer-networks-to-pretheory name)
  (let ((proc-renamer (symbol-append name '-translation-renamer))
	(symbol-prefix (symbol-append name '%)))
    `(define (,proc-renamer sym)
       (concatenate-symbol ',symbol-prefix sym))))

(define (build-network-theory-instance-def-form name)
  (let* ((proc-renamer (symbol-append name '-translation-renamer))
	 (new-theory-name (string->symbol (format nil "PRE-~A-THEORY" name)))
	 (translation-name 'the-kernel-translation)
	 (new-translation-name (symbol-append 'networks-to- new-theory-name)))
    `(def-theory-instance ,new-theory-name
       (source networks)
       (target the-kernel-theory)
       (translation ,translation-name)
       (fixed-theories octets)
       (theorem-prefix ,name)
       (renamer ,proc-renamer)
       (new-translation-name ,new-translation-name))))

(define (build-network-language-def-form name hosts spnets)
  (let ((host-sort (symbol-append name '%hosts))
	(net-sort (symbol-append name '%spnets))
	(language-name (string->symbol (format nil "~A-LANGUAGE" name)))
	(theory-name (string->symbol (format nil "PRE-~A-THEORY" name))))
    `(def-language ,language-name
       (embedded-language ,theory-name)
       (constants 
	,@(map (lambda (hostname) (list hostname host-sort)) hosts)
	,@(map (lambda (netname) (list netname net-sort)) spnets)
	))))
       
(define (build-network-theory-def-form name hosts spnets host-spnet-pairs iface-addresses iface-masks)
  (let ((language-name (string->symbol (format nil "~A-LANGUAGE" name)))
	(irel (symbol-append name '%iface%relation))
	(mask-rel (symbol-append name '%mask%relation))
	(make-iface (symbol-append name '%make%pre%iface))
	(pre-theory-name (string->symbol (format nil "PRE-~A-THEORY" name)))
	(address-rel (symbol-append name '%address%relation))
	(theory-name  (string->symbol (format nil "~A-THEORY" name)))
	(h-number 0)
	(n-number 0)
	(f-number 0))
    `(def-theory ,theory-name
       (component-theories ,pre-theory-name)
       (language ,language-name)
       (distinct-constants ,hosts ,spnets)
       (axioms
	,@(map (lambda (x) 
		 (increment f-number)
		 (destructure (((host net) x))
			      (list (string->symbol (format nil "~A-IFACE-~A" name f-number))
				    (format nil "~A(~A,~A)" irel host net)))
		 )
	       host-spnet-pairs)
	,@(map (lambda (x) 
		 (increment n-number)
		 (destructure (((host net (byte1 byte2 byte3 byte4)) x))
			      (list (string->symbol (format nil "~A-MASK-~A" name n-number))
				    (format nil 
					    "~A(~A(~A,~A), make%address(~A#8, ~A#8, ~A#8, ~A#8))" 
					    mask-rel 

					    make-iface 
					    host 
					    net 

					    byte1 
					    byte2
					    byte3
					    byte4)))
		 )
	       iface-masks)
	,@(map (lambda (x) 
		 (increment h-number)
		 (destructure (((host net (byte1 byte2 byte3 byte4)) x))
			      (list (string->symbol (format nil "~A-ADDR-~A" name h-number))
				    (format nil 
					    "~A(~A(~A, ~A),make%address(~A#8, ~A#8, ~A#8, ~A#8))"
					    address-rel 
					   
					    make-iface
					    host 
					    net

					    byte1
					    byte2
					    byte3
					    byte4
					    
					   )))
		 )
	       iface-addresses)
	))))


(define (build-network-specification-def-forms name host-spnet-addresses host-spnet-masks)
  (let ((host-spnet-pairs '())
	(hosts (make-set (map car host-spnet-addresses)))
	(spnets (make-set (map cadr host-spnet-addresses)))
	(iface-addresses '())
	(iface-masks '()))
    (walk (lambda (x) (let ((p (list (car x) (cadr x))))
			(or (mem? equal? p host-spnet-pairs)
			    (push host-spnet-pairs x))))
	  host-spnet-addresses)
    (walk (lambda (x) (if (caddr x) (push iface-addresses x)))
	  host-spnet-addresses)
    (walk (lambda (x) (if (caddr x) (push iface-masks x)))
	  host-spnet-masks)
    (list (build-renamer-networks-to-pretheory name)
	  (build-network-theory-instance-def-form name)
	  (build-network-language-def-form name hosts spnets)
	  (build-network-theory-def-form name hosts spnets host-spnet-pairs iface-addresses  iface-masks))))

(define (build-network-specification-file name host-spnet-addresses host-spnet-masks outfile)
  (with-open-ports ((pout (open (imps-filespec->string  outfile) '(out))))
		   (walk
		    (lambda (form)
		      (let ((str (with-output-to-string 
				  port
				  (pretty-print form port))))
			(format pout "~A~%~%" (string-downcase str))))
		    (build-network-specification-def-forms name host-spnet-addresses host-spnet-masks))
		   (force-output pout)))

(define (build-network-specification-file-from-input-file  infile outfile)

; Data is in the form of a *single* s-expression:
; (name 
;   (host1 ... hostn) 
;   ((iface host net addrlist))
;   ((iface host net maklist))
; )

  (with-open-ports 
      ((pin (open (imps-filespec->string  infile) '(in))))
    (let ((sexp (read pin)))
      (let ((name (car sexp))
	    (host-spnet-addresses (caddr sexp))
	    (spnet-masks (cadddr sexp)))
	(build-network-specification-file name host-spnet-addresses spnet-masks outfile)))))

(define (build-and-evaluate-network-specification-file name host-spnet-addresses spnet-masks outfile)
  (build-network-specification-file name host-spnet-addresses spnet-masks outfile)
  (load-imps-files (list outfile)))