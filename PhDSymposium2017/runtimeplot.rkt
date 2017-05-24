#lang racket
(require json)
(require math/statistics)
(require plot/pict)

(define (make-func points)
  (define sorted (sort points (lambda (x y)
                                (<= (first x) (first y)))))

  ;; y1 is the value at k=0, y2 is the value at k=1, k is
  ;; our position between the two (from 0 to 1)
  (define (interpolate k y1 y2)
    (+ (* (- 1 k) y1)
       (*      k  y2)))

  ;; At what fraction of the distance from x1 to x2 is x?
  (define (distance x x1 x2)
    (if (= x1 x2)
        0 ;; Arbitrarily
        (let ()
          (define x-norm   (- x  x1))
          (define max-norm (- x2 x1))
          (/ x-norm max-norm))))

  (lambda (x)
    (define lower
      (foldl (lambda (point lowest)
               (if (<= (first point) x)
                   point
                   lowest))
             (first sorted)
             sorted))

    (define upper
      (foldl (lambda (point highest)
               (if (<= (first point) x)
                   highest
                   point))
             (last sorted)
             (reverse sorted)))

    (define k    (distance x (first lower) (first upper)))
    (interpolate k (second lower) (second upper))))

(define input
  (read-json))

(define colors '(black red blue green purple yellow))

(parameterize ([plot-width   500]
               [plot-height  300]
               [plot-x-label "Theory size"]
               [plot-y-label "Runtime (seconds)"]
	       [point-sym 'times]
	       #;[plot-y-transform  log-transform]
	       #;[plot-y-ticks (log-ticks)]
	       #;[plot-x-ticks (linear-ticks #:divisors '(1 5 10))])
  (plot-file
   (foldl (lambda (arg result)
                  (define name  (first  arg))
                  (define files (second arg))
                  (define vals  (map (lambda (f)
                                       (string->jsexpr (file->string f)))
                                     files))

                  ;; Plotting a line requires a function defined for all inputs,
                  ;; but we only have a set of samples, so we must interpolate
                  ;; between them
                  (define point-samples
                    (foldl (lambda (point result)
                             (cons (list (hash-ref point 'size)
                                         (string->number
                                          (hash-ref point 'median))) result))
                           '()
                           vals))

                  ;; Pop the next colour off the list. Ugly, but works.
                  (define color (first colors))
                  (set! colors (cdr colors))

                  (append result
                          (list (points
                                 (map (lambda (point)
                                        (list (hash-ref point 'size)
                                              (string->number
                                               (hash-ref point 'median))))
                                      vals)
                                 #:color color)

                                #;(function (make-func point-samples)
                                          #:color color)

                                (error-bars
                                 (map (lambda (point)
                                        (define l (string->number
                                                   (hash-ref point 'Q1)))
                                        (define u (string->number
                                                   (hash-ref point 'Q3)))
                                        (list (hash-ref point 'size)
                                              (/ (+ l u) 2)
                                              (/ (- u l) 2)))
                                      vals)
                                 #:color color))))
                '()
                (hash-map input (lambda (sys point-files)
                                  (list sys point-files))))
         "runtimes-plot.svg"
         #:x-min 0
         #:x-max 20
         #:y-max 200))
