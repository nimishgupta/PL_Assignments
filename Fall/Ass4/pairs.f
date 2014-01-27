type [[Pair A B]] = (forall C. (A -> B -> C) -> C)

;;

let pair = typfun A ->
             typfun B ->
                fun (x : A) ->
                  fun (y : B) ->
                    typfun C ->
                      fun (r : A -> B -> C) ->
                        r x y

;;

let first = typfun A ->
              typfun B ->
                  fun (p : [[Pair A B]]) ->
                    p <A> (fun (x : A) ->
                             fun (y : B) ->
                               x)

;;

let second = typfun A -> 
               typfun B ->
                  fun (p : [[Pair A B]]) ->
                    p <B> (fun (x : A) ->
                             fun (y : B) ->
                               y)
