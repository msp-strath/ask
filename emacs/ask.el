;;(require 'compile)

;; based on: http://ergoemacs.org/emacs/elisp_syntax_coloring.html

;; syntax table
;;(defvar hacky-syntax-table (make-syntax-table))

(defface labmate-directive
  '((t :foreground "black"
       :background "pale turquoise"
       :weight bold
       ))
  "Face for directives."
  :group 'labmate )

(defface labmate-response-delimiter
  '((t :foreground "black"
       :background "pale green"
       ))
  "Face for response delimiters."
  :group 'labmate )


(defface labmate-response-error
  '((t :foreground "black"
       :background "light salmon"
       :weight bold
       ))
  "Face for errorneous directive responses."
  :group 'labmate )

(defface ask-response-success
  '((t :foreground "black"
       :background "pale green"
       :weight bold
       ))
  "Face for successful directive responses."
  :group 'labmate )

;; define the mode
(define-derived-mode ask-mode fundamental-mode
  "ask mode"
  ;; handling comments
  :syntax-table (make-syntax-table)
  ;; code for syntax highlighting
  (font-lock-add-keywords nil '(("^\s*\\(proven\\|defined\\)[[:space:]]+" . (1 'ask-response-success))))
  (font-lock-add-keywords nil '(("^\s*%>[^%\n]+" 0 'labmate-directive t)))
  (font-lock-add-keywords nil '(("^\s*%<.+" . 'labmate-response-error)))
  (font-lock-add-keywords nil '(("^\s*%<[{}]$" . 'labmate-response-delimiter)))
  ;; Fold generated code
  ;; (hs-minor-mode)

  (setq mode-name "ask")
)



;; Customisation options

(defgroup ask nil
  "A total fragment of Haskell embedded in a proof system."
  :group 'languages)

(defcustom ask-command "ask"
  "The path to the ask command to run."
  :type 'string
  :group 'ask)

(defun ask-run-on-file (ask-file)
  "Run ask on the current buffer and replace the buffer contents with the ask output."

  (save-some-buffers compilation-ask-about-save
                     (when (boundp 'compilation-save-buffers-predicate)
                       compilation-save-buffers-predicate))

  (let* ((res (with-temp-buffer
               (list (call-process ask-command nil
                                   (current-buffer) nil ask-file)
                     (buffer-string))))
         (exitcode (car res))
         (output (cadr res)))
    (if (< exitcode 10)
        (with-current-buffer (current-buffer)
          (let ((old-point (point)))
          (erase-buffer)
          (insert output)
          (goto-char old-point)))
        (message "%s" output))))

;;;###autoload
(defun ask-run (override-options)
  "Run ask on the current file."
  (interactive "P")
  (ask-run-on-file (shell-quote-argument (buffer-file-name)))
)

(define-key ask-mode-map (kbd "<tab>") 'ask-run)

(provide 'ask-mode)
