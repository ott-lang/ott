(define-generic-mode 'ott-mode
  '("%")
  '("metavar" "indexvar" "grammar" "embed" "subrules" "contextrules" "substitutions" "single" "multiple" "freevars" "defns" "defn" "by" "homs" "funs" "fun" "parsing" "begincoqsection" "endcoqsection" "coqvariable" "left" "right" "terminals" "formula" "judgement")
  '(
;    ("\\[\\[.+\\]\\]" . 'font-lock-warning-face)
;    ("\\[\\[[^\\]]+\\]\\]" . 'font-lock-warning-face)
    ("{{\\([^{}]+{[^{}]*}\\)*[^{}]*}}" . 'font-lock-doc-face)
;    ("{{[^}]+}}" . 'font-lock-doc-face)
    ("(\\+.+\\+)" . 'font-lock-keyword-face)
    ("<<.*" . 'font-lock-keyword-face)
    (">>" . 'font-lock-keyword-face)
    ("</" . 'font-lock-keyword-face)
    ("//" . 'font-lock-keyword-face)
    ("IN" . 'font-lock-keyword-face)
    ("/>" . 'font-lock-keyword-face)
    (" | " . 'font-lock-keyword-face)
    (";" . 'font-lock-keyword-face)
    ("<::" . 'font-lock-keyword-face)
    ("_::" . 'font-lock-keyword-face)
    ("::=" . 'font-lock-keyword-face)
    ("::" . 'font-lock-keyword-face)
    ("<=" . 'font-lock-keyword-face)
    )
    (list "\\.ott\\'")
;  '(".keymap\\'" ".map\\'")
  nil
  "Major mode for editing ott format files.")


;    ("\\%.*" . 'font-lock-doc-face)

(provide 'ott-mode)
