(*
  Nicolas ASSOUAD

  Simple test

*)

let rgn1 = newrgn () in

let rec f x = x @ rgn1 in

f 4
