#lang gtlc

((lambda ([f : (Dyn Int -> Int)]) (f f 5))
 (lambda (f n)
   (if (= 0 n)
       1
       (* n (f f (- n 1))))))
