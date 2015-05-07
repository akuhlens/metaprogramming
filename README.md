# Metaprogramming

### The GTLC as the racket #lang gtlc

I think that languages must be installed.

```bash
cd racketGTLC
raco pkg install
```

```racket
#lang gtlc
;; racketGTLC/tests/test10.rkt

((lambda ([f : (Dyn Int -> Int)]) (f f 5))
 (lambda (f n)
   (if (= 0 n)
       1
       (* n (f f (- n 1))))))
       
```
```bash
racket tests/test10.rkt
120
": Int"

tests/runtests

...
```




### The GTLC in as a Well Typed Idris Interpreter
