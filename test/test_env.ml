open Base
open Emelle

let () =
  let env = Env.empty (module Int) in
  match Env.add env 3 "foo" with
  | None -> assert false
  | Some env ->
     match Env.find env 3 with
     | Some ("foo", 0) ->
        Env.in_scope (fun env ->
            match Env.add env 5 "bar" with
            | None -> assert false
            | Some env ->
               match Env.add env 3 "baz" with
               | None -> assert false
               | Some env ->
                  match Env.find env 3 with
                  | Some ("baz", 1) -> ()
                  | _ -> assert false
          ) env;
        begin match Env.find env 3 with
        | Some ("foo", 0) -> ()
        | _ -> assert false
        end
     | _ -> assert false
