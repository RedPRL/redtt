;;; redtt.el --- Major mode for editing redtt proofs and interacting with redtt  -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Jonathan Sterling
;; Copyright (C) 2017  Jonathan Sterling, Favonia
;; Copyright (C) 2018  The RedPRL Development Team

;; Author: Jonathan Sterling <jon@jonmsterling.com>
;; Package-Requires: ((emacs "25.3"))
;; Version: 0.0.1
;; Keywords: languages

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is a major mode for editing redtt developments.  The current
;; editing features include simple syntax highlighting. There is a command to
;; run redtt in a compilation buffer.
;;
;; redtt can be obtained from https://github.com/RedPRL/redtt .
;;
;; Make sure to set the variable `redtt-command' to the location of the
;; redtt binary.

;;; Code:

(require 'cl-lib)

(defgroup redtt nil "redtt" :prefix 'redtt :group 'languages)

(defface redtt-declaration-keyword-face
  '((t (:inherit font-lock-keyword-face))) "Face for redtt's declaration keywords."
  :group 'redtt)

(defface redtt-number-face
  '((t (:inherit font-lock-constant-face))) "Face for redtt's numbers."
  :group 'redtt)

(defface redtt-expression-keyword-face
  '((t (:inherit font-lock-builtin-face))) "Face for redtt's expression keywords."
  :group 'redtt)

(defface redtt-expression-symbol-face
  '((t (:inherit font-lock-builtin-face))) "Face for redtt's expression symbols."
  :group 'redtt)

(defface redtt-tactic-keyword-face
  '((t (:inherit font-lock-builtin-face))) "Face for redtt's tactic keywords."
  :group 'redtt)

(defface redtt-tactic-symbol-face
  '((t (:inherit font-lock-builtin-face))) "Face for redtt's tactic symbols."
  :group 'redtt)

(defface redtt-sequent-keyword-face
  '((t (:inherit font-lock-builtin-face))) "Face for redtt's sequent keywords."
  :group 'redtt)

(defface redtt-sequent-symbol-face
  '((t (:inherit font-lock-builtin-face))) "Face for redtt's sequent symbols."
  :group 'redtt)

(defcustom redtt-command "redtt"
  "The command to be run for redtt."
  :group 'redtt
  :type 'string
  :tag "Command for redtt"
  :options '("redtt"))

(defcustom redtt-mode-hook '(redtt-display-revolutionary-saying)
  "Hook to be run on starting `redtt-mode'."
  :group 'redtt
  :type 'hook
  :options '(redtt-display-revolutionary-saying))

(defvar redtt-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?- "w" table)
    (modify-syntax-entry ?_ "w" table)
    (modify-syntax-entry ?= "w" table)
    (modify-syntax-entry ?' "w" table)
    (modify-syntax-entry ?/  "_ 123" table)
    (modify-syntax-entry ?\n ">" table)
    table)
  "Syntax table for redtt.")

(defconst redtt-declaration-keywords
  '("data" "def" "meta" "normalize" "print")
  "redtt's keywords.")


(defconst redtt-expression-keywords
  '("V" "in" "with" "where" "begin" "end" "let" "tick" "dim" "elim" "fst" "snd" "coe" "com" "pair" "comp" "fun" "hcom" "vproj" "vin" "lam" "next" "prev" "dfix" "fix" "refl" "pre" "kan" "type")
  "redtt's expression keywords.")

(defconst redtt-expression-symbols
  '("->" "~>" "<~" "$" "*" "!" "@" "=" "+" "++" "=>")
  "redtt's expression symbols.")

(defvar redtt-mode-font-lock-keywords
  `(
    ;; Declaration keyword
    (,(regexp-opt redtt-declaration-keywords 'words) 0 'redtt-declaration-keyword-face)

    ;; Numbers
    (,(rx word-start (? "-") (+ digit)) 0 'redtt-number-face)

    ;; Built-in expressions
    (,(regexp-opt redtt-expression-keywords 'words) 0 'redtt-expression-keyword-face)
    (,(regexp-opt redtt-expression-symbols 'nil) 0 'redtt-expression-symbol-face)
    ))

(defconst redtt--compilation-buffer-name
  "*redtt*"
  "The name to use for redtt compilation buffers.")

(defun redtt--compilation-buffer-name-function (_mode)
  "Compute a buffer name for the `redtt-mode' compilation buffer."
  redtt--compilation-buffer-name)

(defun redtt-compile-buffer ()
  "Load the current file into redtt."
  (interactive)
  (let ((filename (buffer-file-name)))
    (if filename
        (progn
          (when (buffer-modified-p) (save-buffer))
          (let* ((dir (file-name-directory filename))
                 (file (file-name-nondirectory filename))
                 (command (concat redtt-command " load-file " file))

                 ;; Emacs compile config stuff - these are special vars
                 (compilation-buffer-name-function
                  'redtt--compilation-buffer-name-function)
                 (default-directory dir))
            (compile command)))
      (error "Buffer has no file name"))))


(defconst redtt--revolutionary-sayings
  '("Between the darkness and the dawn, a red cube rises!"
    "Let's Complete The System of Swedish Moderate Realism!"
    "We Can Prove It!"
    "Uphold Cubical Thought!"
    "Criticize The Old World And Build A New World Using Cubical Thought As A Weapon!")
  "Words of encouragement to be displayed when redtt is initially launched.")

(defun redtt-display-revolutionary-saying ()
  "Display a revolutionary saying to hearten redtt users."
  (interactive)
  (let ((revolutionary-saying
         (nth
          (random (length redtt--revolutionary-sayings))
          redtt--revolutionary-sayings)))
    (message "%s" revolutionary-saying)))

;;;###autoload
(define-derived-mode redtt-mode prog-mode "redtt"
  "Major mode for editing redtt proofs.
\\{redtt-mode-map}"

  (set (make-local-variable 'comment-start) "-- ")

  (setq font-lock-defaults '((redtt-mode-font-lock-keywords) nil nil))

  ;; Bind mode-specific commands to keys
  (define-key redtt-mode-map (kbd "C-c C-l") 'redtt-compile-buffer)

  (set (make-local-variable 'completion-at-point-functions)
       '(redtt-completion-at-point)))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.red\\'" . redtt-mode))

(provide 'redtt)
;;; redtt.el ends here
