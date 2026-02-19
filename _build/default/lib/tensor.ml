open Printf

type 'a tensor = {shape: int array; data: 'a array}

let flat_idx t indices =
  let rec loop acc i =
    if i = Array.length t.shape then acc
    else
      let stride =
        Array.fold_left
          (fun p x -> p * x)
          1
          (Array.sub t.shape (i + 1) (Array.length t.shape - i - 1))
      in
      loop (acc + (indices.(i) * stride)) (i + 1)
  in
  loop 0 0

let get t indices =
  let i = flat_idx t indices in
  t.data.(i)

let set t indices v =
  let i = flat_idx t indices in
  t.data.(i) <- v

let print_tensor t =
  let rank = Array.length t.shape in
  if Array.length t.shape = 0 || Array.fold_left ( * ) 1 t.shape = 0 then
    printf "[]\n"
  else
    let indices = Array.make rank 0 in
    let rec print_recursive depth indent_level =
      let indent_str = String.make (indent_level * 2) ' ' in
      let current_dim_size = t.shape.(depth) in
      if depth = rank - 1 then (
        printf "%s[" indent_str ;
        for i = 0 to current_dim_size - 1 do
          indices.(depth) <- i ;
          printf "%d" (get t indices) ;
          if i < current_dim_size - 1 then printf "; "
        done ;
        printf "]" )
      else (
        printf "%s[\n" indent_str ;
        for i = 0 to current_dim_size - 1 do
          indices.(depth) <- i ;
          print_recursive (depth + 1) (indent_level + 1) ;
          if i < current_dim_size - 1 then printf ";\n" else printf "\n"
        done ;
        printf "%s]" indent_str )
    in
    print_recursive 0 0 ; printf "\n"

let random_int_tensor shape =
  let total = Array.fold_left ( * ) 1 shape in
  let data =
    Array.init total (fun _ -> Random.int_in_range ~min:(-10000) ~max:10000)
  in
  {shape; data}
