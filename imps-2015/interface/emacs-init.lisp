(defvar imps-source-files (substitute-in-file-name "/home/jt/imps/oolong/"))

(defun in-vicinity (dir pathname)
  (substitute-in-file-name (expand-file-name (concat dir pathname))))

(setq load-path 
	  (cons (in-vicinity imps-source-files "../el")
		load-path))


(require 'scheme)
(require 'backquote)
(require 'shell)
(require 'font-lock)
(mapcar #'(lambda (x) 
	    (byte-compile-file 
	     (in-vicinity imps-source-files (concat "../el/" (format "%s.el" x)))))
	'(pre-imps tea imps process-filter theory-information sqns imps-edit protocols 
		   deduction-graphs imps-commands imps-manual
		   imps-df-templates imps-proof-edit imps-fsf-support 
		   imps-x-support imps-lucid-support
		   imps-tutorial micro-exercises def-form-edit))


    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
