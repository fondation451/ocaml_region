(*
  Nicolas ASSOUAD

  Simple test

*)

let rgn1 = newrgn () in

let rec g x = x @ rgn1 in

let rec f x = g x @ rgn1 in

f 4
