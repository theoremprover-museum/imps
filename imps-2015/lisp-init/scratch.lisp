(let ((imps-pathname "~/imps/"))
  (set (default-pathname) (make-pathname (format nil "~Aoolong/" imps-pathname) nil "fas"))
  (set (symbol-pathname 'oolong-compiled) (make-pathname (format nil "~Aoolong/" imps-pathname) nil "fas"))
  (load '(user imps))
  (load-imps)
  (set (symbol-pathname 'imps) (make-pathname  imps-pathname nil "t"))
  (load-section foundation))

(block (lset imps-pathname "~/imps/") (set (default-pathname) (make-pathname (format nil "~Aoolong/" imps-pathname) nil "ool")) (set (symbol-pathname 'oolong-compiled) (make-pathname (format nil "~Aoolong/" imps-pathname) nil "ool")) (load '(user imps)) (load-imps) (load '(oolong-compiled user/test-imps)) (set (symbol-pathname 'imps) (make-pathname  imps-pathname nil "t")) (set (emacs-process-filter?) value-false) (set (proof-log-port) (standard-output)) (do-test-suite 'whopper) (quit))