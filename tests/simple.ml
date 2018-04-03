(*
  Nicolas ASSOUAD

  Simple test

*)

let r1 = newrgn () in

let rec g x r = (x, x) @ r @ r1 in

let rec f x r = g x r @ r1 in

snd (f (4, 4) @ r1 r1)
