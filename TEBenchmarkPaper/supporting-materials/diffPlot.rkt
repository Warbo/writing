#lang racket
(require json)
(require math/statistics)
(require plot/pict)

;; We want the 95% confidence interval
(define confidence 0.95)
(define alpha (/ (- 1 confidence) 2))

;; Look up alpha in standard table of z scores
(define z-score 1.96)

(define (sassoc k l)
  (second (assoc k l)))

(define input
  (read-json))

(define data
  (hash-map input
            (lambda (sys sizes)
              (list sys
                    (hash-map (string->jsexpr (file->string sizes))
                              (lambda (size diffs)
                                (define m    (mean diffs))
                                (define var  (variance diffs))
                                (define serr (/ var (sqrt (length diffs))))
                                `((mean        ,m)
                                  (upper-95    ,(+ m (* z-score serr)))
                                  (lower-95    ,(- m (* z-score serr)))
                                  (sample-size ,(string->number
                                                 (symbol->string size))))))))))

(define colors '(black red blue green purple yellow))

(parameterize ([plot-width    500]
               [plot-height   500]
               [plot-x-label  #f]
               [plot-y-label  #f])
  (plot-file (foldl (lambda (sys result)
                      (define name (first  sys))
                      (define vals (second sys))

                      ;; Pop the next colour off the list. Ugly, but works.
                      (define color (first colors))
                      (set! colors (cdr colors))

                      (append result
                              (list (points
                                     (map (lambda (point)
                                            (list (sassoc 'sample-size point)
                                                  (sassoc 'mean        point)))
                                          vals)
                                     #:color color)
                                    (error-bars
                                     (map (lambda (point)
                                            (define l (sassoc 'lower-95 point))
                                            (define u (sassoc 'upper-95 point))
                                            (list (sassoc 'sample-size point)
                                                  (/ (+ l u) 2)
                                                  (/ (- u l) 2)))
                                          vals)
                                     #:color color))))
                    '()
                    data)
             "diffPlot.svg"))

;(eprintf (~a data))

;(plot )

(exit 1)
