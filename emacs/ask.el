;;(require 'compile)

;; based on: http://ergoemacs.org/emacs/elisp_syntax_coloring.html

;; syntax table
;;(defvar hacky-syntax-table (make-syntax-table))

(defface ask-primary-keyword
  '((t :foreground "black"
       :background "orange"
       :weight bold
       ))
  "Face for keywords (prove, define)."
  :group 'ask )

(defface ask-assumption
  '((t :foreground "black"
       :background "orchid"
       :weight bold
       ))
  "Face for given."
  :group 'ask )


(defface ask-secondary-keyword
  '((t :foreground "black"
       :weight bold
       ))
  "Face for \"glue\" keywords (by, where, ...)."
  :group 'ask )

(defface ask-response-success
  '((t :foreground "black"
       :background "pale green"
       :weight bold
       ))
  "Face for successful directive responses."
  :group 'ask )

(defvar ask-syntax-table
  (let ((st (make-syntax-table)))
    ;; comments based on https://stackoverflow.com/questions/20731684/elisp-syntax-table-comments-for-haskell-style-comments
    (modify-syntax-entry ?\{  "(}1nb" st)
    (modify-syntax-entry ?\}  "){4nb" st)
    (modify-syntax-entry ?-  "_ 123" st)
    (modify-syntax-entry ?\n ">" st)
    st))

;; define the mode
(define-derived-mode ask-mode fundamental-mode
  "ask mode"
  ;; handling comments
  :syntax-table ask-syntax-table
  ;; code for syntax highlighting
  (font-lock-add-keywords nil '(("^\s*\\(given.*\\)?\\(proven\\|defined\\)[[:space:]]+" . (2 'ask-response-success))))
  (font-lock-add-keywords nil '(("^\s*\\(given.*\\)?\\(prove\\|define\\)[[:space:]]+" . (2 'ask-primary-keyword))))
  (font-lock-add-keywords nil '(("\\(data\\|prop\\|where\\|from\\|by\\|inductively\\|tested\\|test\\|under\\)" . (1 'ask-secondary-keyword))))
  (font-lock-add-keywords nil '(("^\s*\\(given\\)[[:space:]]+" . (1 'ask-assumption))))
  (font-lock-add-keywords nil '(("[[:space:]]+\\(given\\)\s*$" . (1 'ask-secondary-keyword))))

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

(defun ask-replace-current-word-query (query replace)
  "Replace current word with prompted word."
  (interactive
   (let ((q (current-word)))
   (list
    q
    (read-string (concat "Replace " q " by: ")))))
  (save-excursion
    (beginning-of-line)
    (query-replace query replace t)))

(define-key ask-mode-map (kbd "<tab>") 'ask-run)
(define-key ask-mode-map (kbd "C-c C-r") 'ask-replace-current-word-query)

(provide 'ask-mode)
