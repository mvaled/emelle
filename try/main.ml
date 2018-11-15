open Base
open Emelle

let () =
  Dom_html.window##.onload :=
    Dom.handler (fun _ ->
        let textarea =
          match
            Dom_html.getElementById_coerce "editor" Dom_html.CoerceTo.textarea
          with
          | None -> assert false
          | Some textarea -> textarea
        in
        let button = Dom_html.getElementById "compile" in
        button##.onclick :=
          Dom.handler (fun _ ->
              begin match
                let program = textarea##.value in
                let bytestr = Js.to_bytestring program in
                Parser.file Lexer.expr (Lexing.from_string bytestr)
                |> Pipeline.compile (Hashtbl.create (module String)) "main"
              with
              | Ok _ ->
                 Caml.print_endline "OK!"
              | Error _ ->
                 Caml.print_endline "ERROR!"
              end;
              Js._true
            );
        Caml.print_endline "loaded";
        Js._true
      )
