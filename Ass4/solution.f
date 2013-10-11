type [[Triple A B C]] = (forall D. (A -> B -> C -> D) -> D)

;;

let triple = typfun A -> 
               typfun B -> 
                 typfun C -> 
                   fun (x : A) -> 
                     fun (y : B) -> 
                       fun (z : C) -> 
                         typfun D -> 
                           fun (r : A -> B -> C -> D) -> 
                             r x y z

;;


let Proj1 = typfun A ->
              typfun B ->
                typfun C ->
                  fun (p : [[Triple A B C]]) ->
                    p <A> (fun (x : A) ->
                             fun (y : B) -> 
                               fun (z : C) -> 
                                 x)

;;


let Proj2 = typfun A ->
              typfun B ->
                typfun C ->
                  fun (p : [[Triple A B C]]) ->
                    p <B> (fun (x : A) ->
                             fun (y : B) -> 
                               fun (z : C) -> 
                                 y)

;;

let Proj3 = typfun A ->
              typfun B ->
                typfun C ->
                  fun (p : [[Triple A B C]]) ->
                    p <C> (fun (x : A) ->
                             fun (y : B) -> 
                               fun (z : C) -> 
                                 z)

;;
