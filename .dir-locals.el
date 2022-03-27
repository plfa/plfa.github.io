;;; Directory Local Variables
;;; For more information see
;;;   - (info "(emacs) Directory Variables") or
;;;   - https://www.gnu.org/software/emacs/manual/html_node/emacs/Directory-Variables.html

;; The .dir-locals.el file should hold a specially-constructed list,
;; and with this list, we turn off auto-fill-mode for all files in PLFA project:
((nil . ((eval . (turn-off-auto-fill)))))
