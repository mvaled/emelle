open Base

let rec lower symtbl =
  let open Result.Monad_infix in
  function
  | Term.Ann { term; _ } -> lower symtbl term
  | Term.App(f, x) ->
     lower symtbl f >>= fun f ->
     lower symtbl x >>| fun x ->
     Lambda.App(f, x)
  | Term.Case(discriminant, discriminants, cases) ->
     List.fold_right ~f:(fun (first_pattern, rest_patterns, term) acc ->
         acc >>= fun list ->
         lower symtbl term >>| fun lambda ->
         Pattern.{ first_pattern; rest_patterns; action = lambda}::list
       ) ~init:(Ok []) cases >>= fun matrix ->
     Pattern.decision_tree_of_matrix
       (let (occurrences, _) =
          List.fold ~f:(fun (list, i) _ ->
              ([i]::list, i + 1)
            ) ~init:([], 0) (discriminant::discriminants)
        in occurrences)
       symtbl matrix
     >>= fun decision_tree ->
     lower symtbl discriminant >>= fun discriminant ->
     List.fold_right ~f:(fun term acc ->
         acc >>= fun list ->
         lower symtbl term >>| fun lambda ->
         lambda::list
       ) ~init:(Ok []) discriminants >>| fun discriminants ->
     Lambda.Case(discriminant, discriminants, decision_tree)
  | Term.Extern_var id -> Ok (Lambda.Extern_var id)
  | Term.Lam(reg, term) ->
     lower symtbl term >>| fun lambda ->
     Lambda.Lam(reg, lambda)
  | Term.Let(reg, def, body) ->
     lower symtbl def >>= fun def ->
     lower symtbl body >>| fun body ->
     Lambda.Let(reg, def, body)
  | Term.Let_rec(bindings, body) ->
     List.fold_right ~f:(fun (reg, def) acc ->
         acc >>= fun list ->
         lower symtbl def >>| fun lambda ->
         (reg, lambda)::list
       ) ~init:(Ok []) bindings >>= fun bindings ->
     lower symtbl body >>| fun body ->
     Lambda.Let_rec(bindings, body)
  | Term.Var reg -> Ok (Lambda.Local_var reg)
