;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

;; Disable auto-fill
(turn-off-auto-fill)
(remove-hook 'text-mode-hook #'turn-on-auto-fill)


;; Disable auto-fill for Aquamacs
(when (featurep 'aquamacs)
  (remove-hook 'text-mode-hook 'auto-detect-wrap))
