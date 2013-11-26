let rec eval (e : exp) (env : env) : value -> match e with
  | Int n -> n
  | Bool b -> b
  | BinOp (op, e1, e2) ->
      let v1 = eval e1 env in
      let v2 = eval e2 env in
      app_binary_op (op, v1, v2)

  | If (e1, e2, e3) ->
      if eval e1 env then eval e2 env else eval e3 env

  | Id x -> Env.lookup x env

  | Let (x, with_e, in_e) ->
      let env' = Env.bind x (eval with_e env) env in
      eval in_e env'

  | Fun (x, _, body) -> Closure (x, body, env)

  | App (e1, e2) ->
      match eval e1 env, eval e2 env with 
        | Closure (x, body, env'), v -> 
            let env'' = Env.bind x v env' in
            eval body env''
        | _ -> failwith "Expected a function"

  | Empty t -> Empty (t)
  | Cons (e1, e2) ->
      let v1 = eval e1 in 
      let v2 = eval e2 in
      Cons (v1, v2)

  | Head e -> match eval e env with
      | Cons (v1, v2) -> v1
      | _ -> failwith "List expected"

  | Tail e -> match eval e env with
      | Cons (v1, v2) -> v2
      | _ -> failwith "List expectd"

  | IsEmpty e -> match eval e env with
      | Cons _ -> false
      | Empty _ -> true
      | _ -> failwith "List expected"

  | Tuple e_list -> Tuple (List.for_all (eval env) e_list)

  | Proj (e, i) -> match eval e env with
      | Tuple (vlist) -> List.nth vlist i
      | _ -> failwith "Expected Tuple"
                         
