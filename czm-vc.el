;;; czm-vc.el --- VC helpers                         -*- lexical-binding: t; -*-

;; Copyright (C) 2026  Paul D. Nelson

;; Author: Paul D. Nelson <ultrono@gmail.com>
;; Keywords: vc

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; Small helper commands for VC / Git and Embark integrations.

;;; Code:

(require 'subr-x)

(declare-function vc-git--run-command-string "vc-git" (file &rest args))
(declare-function vc-git-command "vc-git" (buffer okstatus file-or-list &rest flags))
(declare-function vc-git--assert-allowed-rewrite "vc-git" (rev))
(declare-function vc-git--call "vc-git" (infile buffer command &rest args))
(declare-function vc-git--empty-db-p "vc-git" ())
(declare-function vc-create-repo "vc" (backend &optional directory))
(declare-function vc-read-revision "vc" (prompt &optional files backend default initial-input))
(declare-function vc-print-root-log "vc" (&optional limit))
(declare-function vc-print-branch-log "vc" (working-revision &optional verbose))
(declare-function vc-revert "vc" (&optional file rev))
(declare-function vc-root-dir "vc" (&optional dir))
(declare-function vc-responsible-backend "vc" (file))
(declare-function vc-dir-current-file "vc-dir" ())
(declare-function vc-dir-marked-files "vc-dir" ())
(declare-function log-view-current-tag "log-view" ())
(declare-function log-view-current-entry "log-view" (&optional pos move))
(declare-function log-view-copy-revision-as-kill "log-view" ())
(declare-function project-root "project" (project))

(defvar vc-git-shortlog-switches)
(defvar vc-revert-show-diff)
(defvar vc-suppress-confirm)
(defvar embark-keymap-alist)
(defvar embark-target-finders)

;; Internal helpers
(defun czm-vc--assert-git-working-tree (&optional dir)
  "Signal an error unless DIR (or `default-directory') is in a Git worktree."
  (require 'vc)
  (let* ((dir (or dir default-directory))
         (backend (ignore-errors (vc-responsible-backend dir))))
    (unless (eq backend 'Git)
      (user-error "Not in a Git working tree"))))

(defun czm-vc--assert-safe-git-revision (rev &optional buffer dir)
  "Return REV trimmed, after basic safety checks and `git rev-parse --verify'.
When DIR is non-nil, run Git commands from that directory."
  (require 'vc-git)
  (let* ((dir (or dir default-directory))
         (default-directory (file-name-as-directory (expand-file-name dir)))
         (trimmed (string-trim (or rev ""))))
    (czm-vc--assert-git-working-tree dir)
    (when (string-empty-p trimmed)
      (user-error "Empty revision"))
    ;; Disallow leading '-' to avoid Git option injection in revision positions.
    (when (string-prefix-p "-" trimmed)
      (user-error "Invalid revision (must not start with '-')"))
    ;; Disallow whitespace/control chars which can confuse command argument parsing.
    (when (string-match-p "[[:space:]\n\r]" trimmed)
      (user-error "Invalid revision (must not contain whitespace)"))
    ;; Allow either a single commit-ish (e.g. HEAD~6) or a revision range
    ;; (e.g. HEAD~6..HEAD).  For ranges, verify both endpoints.
    ;;
    ;; Use `vc-git--call' directly so we don't accidentally append FILE-OR-LIST
    ;; arguments (which can break verification in some setups).
    (let ((range-pos (string-match "\\.\\.\\.?" trimmed)))
      (if (not range-pos)
          (let ((status (vc-git--call nil buffer "rev-parse" "--verify"
                                      (format "%s^{commit}" trimmed))))
            (unless (zerop status)
              (when (bufferp buffer) (pop-to-buffer buffer))
              (user-error "Not a commit-ish: %s" trimmed)))
        (let ((lhs (substring trimmed 0 range-pos))
              (rhs (substring trimmed (match-end 0))))
          (when (or (string-empty-p lhs) (string-empty-p rhs))
            (user-error "Revision range must specify both ends: %s" trimmed))
          (dolist (end (list lhs rhs))
            (let ((status (vc-git--call nil buffer "rev-parse" "--verify"
                                        (format "%s^{commit}" end))))
              (unless (zerop status)
                (when (bufferp buffer) (pop-to-buffer buffer))
                (user-error "Not a commit-ish: %s" end)))))))
    trimmed))

;;;###autoload
(defun czm-vc-project-format-patch-last-commit (&optional arg)
  "Create a patch file from the last commit in the current project.
With prefix argument ARG, prompt for a specific commit.
The patch is saved in the project root directory and opened in a buffer."
  (interactive "P")
  (require 'project)
  (require 'vc-git)
  (let* ((project (project-current t))
         (root (project-root project))
         (default-directory root)
         (commit (if arg
                     (vc-read-revision "Format patch from (commit/range): " nil 'Git "HEAD")
                   "HEAD")))
    (czm-vc--assert-git-working-tree root)
    (when (vc-git--empty-db-p)
      (user-error "No commits exist in this Git repository"))
    ;; Only verify user-provided revisions.  For the default `HEAD', let
    ;; `git format-patch' be the source of truth.
    (when arg
      (setq commit (czm-vc--assert-safe-git-revision commit nil root)))
    (message "Generating patch from %s..." commit)
    (let ((filename
           (string-trim
            (with-temp-buffer
              (if (zerop
                   (if (string-match-p "\\.\\.\\.?" commit)
                       (vc-git--call nil t "format-patch" commit)
                     (vc-git--call nil t "format-patch" "-1" commit)))
                  (buffer-string)
                (user-error "Failed to generate patch from %s" commit))))))
      (when (string-empty-p filename)
        (user-error "git format-patch produced no output; no patch file created"))
      (find-file (expand-file-name filename root))
      (diff-mode)
      (message "Patch saved as %s" filename))))

;;;###autoload
(defun czm-vc-create-directory-with-git-repo (dir)
  "Create directory DIR, initialize a Git repository, and open it in Dired."
  (interactive
   (list (read-file-name "Create directory with Git repo: "
                         default-directory default-directory
                         nil nil)))
  (require 'vc)
  (make-directory dir t)
  (let ((default-directory (file-name-as-directory (expand-file-name dir))))
    (vc-create-repo 'Git)
    (dired default-directory)))

;;;###autoload
(defun czm-vc-diff-dired-changed-files ()
  "Open Dired showing files mentioned in the current Diff buffer."
  (interactive)
  (unless (derived-mode-p 'diff-mode)
    (user-error "Not in a Diff buffer"))
  (require 'vc)
  (let* ((files nil)
         (root (or (vc-root-dir) default-directory)))
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward "^\\+\\+\\+ [ab]/\\(.*\\)" nil t)
        (let ((file (match-string 1)))
          (push file files))))
    (if files
        (dired (cons root (nreverse files)))
      (user-error "No files found in diff"))))

;;;###autoload
(defun czm-vc-git-drop-whitespace-changes ()
  "Revert whitespace-only edits in the current buffer's file."
  (interactive)
  (require 'vc)
  (require 'vc-git)
  (let ((file (buffer-file-name)))
    (unless file (user-error "Buffer not visiting a file"))
    (when (buffer-modified-p)
      (user-error "Save the buffer before dropping whitespace-only changes"))
    (czm-vc--assert-git-working-tree file)
    (let ((staged-status (vc-git-command nil 1 nil "diff" "--cached" "--quiet" "--" file)))
      (when (= staged-status 1)
        (user-error "File has staged changes; aborting")))
    (let ((patch (vc-git--run-command-string file "diff" "-w" "HEAD" "--" file))
          (vc-revert-show-diff nil)
          (vc-suppress-confirm t))
      (if (string-empty-p patch)
          (message "No non-whitespace edits to keep")
        (let* ((backup (with-temp-buffer
                         (insert-file-contents file)
                         (buffer-string)))
               (patch-file (make-nearby-temp-file "vc-drop-white-")))
          (unwind-protect
              (progn
                (with-temp-file patch-file (insert patch))
                (unless (zerop (vc-git-command nil t file "apply" "--check" "--"
                                               (file-local-name patch-file)))
                  (user-error "Patch would not apply cleanly; aborting"))
                (vc-revert)
                (unless (zerop (vc-git-command nil t file "apply" "--"
                                               (file-local-name patch-file)))
                  (let ((inhibit-read-only t))
                    (erase-buffer)
                    (insert backup)
                    (write-region (point-min) (point-max) file nil 0)
                    (set-buffer-modified-p nil))
                  (user-error "Failed to apply patch; restored original file"))
                (unless (zerop (vc-git-command nil t file "apply" "--cached" "--"
                                               (file-local-name patch-file)))
                  (user-error "Failed to stage non-whitespace changes"))
                (revert-buffer nil t))
            (delete-file patch-file)))))))

;;;###autoload
(defun czm-vc-root-shortlog-all (&optional limit)
  "Show a one-line, graph-style Git log across all branches.
With numeric prefix argument LIMIT, show that many commits
The default is `vc-log-show-limit' if > 0."
  (interactive
   (list (when current-prefix-arg
           (prefix-numeric-value current-prefix-arg))))
  (let ((vc-git-shortlog-switches '("--all")))
    ;; For a repo root this automatically gives the short view.
    (vc-print-root-log limit)))

;;;###autoload
(defun czm-vc-dir-dired-marked ()
  "Open Dired with marked files in `vc-dir' (or file at point)."
  (interactive)
  (require 'vc-dir)
  (let ((files (or (vc-dir-marked-files)
                   (list (vc-dir-current-file)))))
    (if (null files)
        (user-error "No files marked or at point")
      (dired (cons default-directory files)))))

;;;###autoload
(defun czm-vc-log-view-copy-revision-or-range-as-kill ()
  "Copy commit at point, or copy commit range when region is active."
  (interactive)
  (if-let* ((_region (use-region-p))
            (top (cadr (log-view-current-entry (region-beginning))))
            (bottom (cadr (log-view-current-entry (region-end))))
            ((not (equal top bottom))))
      (let ((range (format "%s..%s" bottom top)))
        (deactivate-mark)
        (kill-new range)
        (message "Copied \"%s\" to kill ring." range))
    (log-view-copy-revision-as-kill)))

;;;###autoload
(defun czm-vc-embark-show-commit (commit)
  "Show COMMIT via `vc-print-branch-log', constraining it to COMMIT^!."
  (interactive (list (or (thing-at-point 'symbol t)
                         (read-string "Commit: "))))
  (require 'vc)
  (let* ((root (or (ignore-errors (vc-root-dir)) default-directory))
         (default-directory root)
         (trimmed (czm-vc--assert-safe-git-revision commit))
         (range (if (string-suffix-p "^!" trimmed)
                    trimmed
                  (concat trimmed "^!"))))
    (vc-print-branch-log range)))

;;;###autoload
(defun czm-vc-embark-copy-commit (commit)
  "Copy COMMIT to the kill ring."
  (interactive (list (or (thing-at-point 'symbol t)
                         (user-error "No commit at point"))))
  (kill-new commit)
  (message "Copied %s" (substring commit 0 (min 12 (length commit)))))

(defun czm-vc-embark-target-git-commit-at-point ()
  "Embark target finder for Git commits at point."
  (let ((s (thing-at-point 'symbol t)))
    (when (and s (string-match-p "\\`[0-9a-f]\\{7,40\\}\\'" s))
      (cons 'git-commit s))))

;;;###autoload
(defun czm-vc-embark-setup ()
  "Set up Embark targets/actions for Git commits."
  (require 'embark)
  (add-to-list 'embark-target-finders #'czm-vc-embark-target-git-commit-at-point t)

  (defvar-keymap czm-vc-embark-git-commit-map
    :doc "Embark actions for Git commits."
    "RET" #'czm-vc-embark-show-commit
    "l"   #'czm-vc-embark-show-commit
    "w"   #'czm-vc-embark-copy-commit)

  (add-to-list 'embark-keymap-alist
               '(git-commit . czm-vc-embark-git-commit-map)))

;;;###autoload
(defun czm-vc-diff-staged ()
  "Show Git staged changes (\"git diff --cached\")."
  (interactive)
  (require 'vc-git)
  (let* ((root (or (ignore-errors (vc-root-dir))
                   default-directory))
         (backend (ignore-errors (vc-responsible-backend root)))
         (buffer (get-buffer-create "*vc-diff-staged*")))
    (unless (eq backend 'Git)
      (user-error "Not in a Git working tree"))
    (with-current-buffer buffer
      (setq-local default-directory root)
      (let ((inhibit-read-only t))
        (erase-buffer)
        (vc-git-command buffer 0 root "diff" "--cached")
        (when (zerop (buffer-size))
          (insert "No staged changes.\n"))
        (goto-char (point-min))
        (diff-mode)))
    (pop-to-buffer buffer)))

(defun czm-vc-git--read-fixup-commit ()
  "Read a commit (hash/ref) to fix up.

If called from `log-view-mode', default to `log-view-current-tag'."
  (require 'vc)
  (let* ((root (or (ignore-errors (vc-root-dir)) default-directory))
         (backend (ignore-errors (vc-responsible-backend root)))
         (default (when (derived-mode-p 'log-view-mode)
                    (ignore-errors (log-view-current-tag)))))
    (unless (eq backend 'Git)
      (user-error "Not in a Git working tree"))
    (read-string (if default
                     (format "Fixup commit (default %s): " default)
                   "Fixup commit: ")
                 nil nil default)))

;; Git helpers
(defun czm-vc-git--commit-parents (commit)
  "Return a list of parent commits for COMMIT."
  (require 'vc-git)
  (let* ((s (vc-git--run-command-string nil "show" "-s" "--format=%P" commit))
         (s (string-trim (or s ""))))
    (if (string-empty-p s) nil (split-string s " " t))))

;;;###autoload
(defun czm-vc-git-fixup-staged (commit)
  "Create a Git fixup commit for COMMIT using staged changes, then autosquash.
Roughly, it runs:
  git diff --cached --quiet
  git commit --fixup=COMMIT --no-edit
  GIT_SEQUENCE_EDITOR=true git rebase --autostash --autosquash -i BASE
where BASE is COMMIT's parent, or `--root' if COMMIT is a root commit."
  (interactive (list (czm-vc-git--read-fixup-commit)))
  (require 'vc)
  (require 'vc-git)
  (let* ((root (or (ignore-errors (vc-root-dir)) default-directory))
         (backend (ignore-errors (vc-responsible-backend root)))
         (buf (get-buffer-create "*vc-git-fixup*")))
    (unless (eq backend 'Git)
      (user-error "Not in a Git working tree"))
    (let ((default-directory root))
      (setq commit (czm-vc--assert-safe-git-revision commit buf))
      (with-current-buffer buf
        (let ((inhibit-read-only t))
          (erase-buffer)))

      (let ((staged-status (vc-git-command buf 1 nil "diff" "--cached" "--quiet")))
        (cond
         ((= staged-status 0) (user-error "No staged changes"))
         ((/= staged-status 1)
          (pop-to-buffer buf)
          (error "Git diff --cached --quiet failed (%s)" staged-status))))

      (when (fboundp 'vc-git--assert-allowed-rewrite)
        (vc-git--assert-allowed-rewrite commit))

      (let* ((parents (czm-vc-git--commit-parents commit))
             (base (pcase (length parents)
                     (0 :root)
                     (1 (car parents))
                     (_ :merge))))
        (when (eq base :merge)
          (pop-to-buffer buf)
          (error "Cannot autosquash fixup commits onto merge commits"))

        (let ((existing
               (with-output-to-string
                 (with-current-buffer standard-output
                   (apply #'vc-git-command standard-output 0 nil
                          "log" "--oneline" "-E"
                          "--grep" "^(squash|fixup|amend)! "
                          (if (eq base :root)
                              nil
                            (list (format "%s.." base))))))))
          (when (and (length> existing 0)
                     (not (yes-or-no-p
                           "Rebase may --autosquash your other squash!/fixup!/amend!; proceed? ")))
            (user-error "Aborted")))

        (let ((status (vc-git-command buf 0 nil
                                      "commit" (format "--fixup=%s" commit) "--no-edit")))
          (unless (zerop status)
            (pop-to-buffer buf)
            (error "Git commit --fixup failed (%s)" status)))

        (with-environment-variables (("GIT_SEQUENCE_EDITOR" "true"))
          (let ((status (apply #'vc-git-command buf 0 nil
                               "rebase" "--autostash" "--autosquash" "-i"
                               (if (eq base :root) (list "--root") (list base)))))
            (unless (zerop status)
              (pop-to-buffer buf)
              (error "Git rebase --autosquash failed (%s)" status))))

        (message "Fixup + autosquash complete for %s" commit)
        (when (derived-mode-p 'log-view-mode)
          (revert-buffer nil t))))))

(provide 'czm-vc)
;;; czm-vc.el ends here
