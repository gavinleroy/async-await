
let rec reduce _par  grain g z (lo, hi) f = 
  let n = hi - lo in 
  if n <= grain then 
    let rec loop acc i = 
      if i >= hi then acc else loop (g acc (f i)) (i + 1) in loop z lo 
  else 
    let mid = lo + n / 2 in 
    let l, r = Parallel.fork_join2 _par 
      (fun _par -> reduce _par grain g z (lo, mid) f)
      (fun _par -> reduce _par grain g z (mid, hi) f)
    in 
    g l r


let () = 
  Printf.printf "reduce.ml loaded\n"
