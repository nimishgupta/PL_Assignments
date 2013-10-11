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


type [[Bool]] = forall R . R -> R -> R

;;

let true = typfun R -> fun (x : R) -> fun (y : R) -> x

;;

let false = typfun R -> fun (x : R) -> fun (y : R) -> y

;;

let if = typfun R -> 
           fun (cond : [[Bool]]) ->
             fun (true_branch : R) ->
               fun (false_branch : R) ->
                 cond<R> true_branch false_branch;;

let and = fun (e1 : [[Bool]]) ->
            fun (e2 : [[Bool]]) ->
              typfun R ->
                fun (x : R) ->
                  fun (y : R) ->
                    e1 <R> (e2 <R> x y) y

;;


let or = fun (e1 : [[Bool]]) ->
           fun (e2 : [[Bool]]) ->
             typfun R ->
               fun (x : R) ->
                 fun (y : R) ->
                   e1 <R> x (e2 <R> x y)
                   
;;


let not = fun (e : [[Bool]]) ->
            typfun R ->
              fun (x : R) ->
                fun (y : R) ->
                  e <R> y x

;;

let nand = fun (e1 : [[Bool]]) ->
            fun (e2 : [[Bool]]) ->
              typfun R ->
                fun (t : R) ->
                  fun (f : R) ->
                    (not (and e1 e2)) <R> t f
                    
;;

let xor = fun (e1 : [[Bool]]) ->
           fun (e2 : [[Bool]]) ->
              typfun R ->
                fun (t : R) ->
                  fun (f : R) ->
                    (or (and e1 (not e2)) (and (not e1) e2)) <R> t f

;;

