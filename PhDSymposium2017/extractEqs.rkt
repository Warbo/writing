(enter! (file "DEFS_LOCATION"))

(write-json
 (map (lambda (given)
        (match given
          [(hash-table ('names  namesStr)
                       ('rep    rep)
                       ('size   size)
                       ('stdout eqs))
           (list namesStr rep size eqs
                 (fix-json-for-output
                  (conjectures-from-sample (parse-json-equations
                                            (jsexpr->string eqs))
                                           (map (lambda (s) (decode-name (string->symbol s)))
                                                (string-split namesStr "\n")))))]))
      (string->jsexpr (port->string))))
