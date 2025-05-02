#lang racket

(require
  "monads.rkt")

(provide pp-srcloc)

;; TODO: Multiline spans
(define/contract (pp-srcloc l)
  (-> srcloc? (or/c string? #f))
  (do/or-false
    let maybe-path = (srcloc-source l)
    path <- (if (path? maybe-path) maybe-path #f)
    line <- (srcloc-line l)
    column <- (srcloc-column l)
    span <- (srcloc-span l)
    let port = (open-input-file path #:mode 'text)
    let line-text = (list-ref (port->lines port) (- line 1))
    let underline = (build-string (+ column span) (λ (n) (if (< n column) #\space #\^)))
    let line-text-width = (string-length (number->string line))
    let filler = (build-string line-text-width (λ (_) #\space))
    (format "~a | ~a~n~a | ~a" line line-text filler underline)))
