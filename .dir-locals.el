;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

;; Disable auto-fill-mode for PLFA
(turn-off-auto-fill)
(remove-hook 'text-mode-hook #'turn-on-auto-fill)
