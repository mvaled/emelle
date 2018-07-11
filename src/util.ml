module Option = struct
  type 'a t = 'a option
  let map f = function
    | Some x -> Some (f x)
    | None -> None
  let bind m f =
    match m with
    | Some x -> f x
    | None -> None
  let return x = Some x
end

module Result = struct
  type ('a, 'b) t = ('a, 'b) result
  let map f = function
    | Ok x -> Ok (f x)
    | Error e -> Error e
  let bind m f =
    match m with
    | Ok x -> f x
    | Error e -> Error e
  let return x = Ok x
end
