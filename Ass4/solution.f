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


let triple_proj1 = typfun A ->
              typfun B ->
                typfun C ->
                  fun (p : [[Triple A B C]]) ->
                    p <A> (fun (x : A) ->
                             fun (y : B) -> 
                               fun (z : C) -> 
                                 x)

;;


let triple_proj2 = typfun A ->
              typfun B ->
                typfun C ->
                  fun (p : [[Triple A B C]]) ->
                    p <B> (fun (x : A) ->
                             fun (y : B) -> 
                               fun (z : C) -> 
                                 y)

;;

let triple_proj3 = typfun A ->
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


type [[Foo A]] = (forall R. (A -> A -> R) -> R -> R)

;;

let bar = typfun A ->
            fun (x : A) ->
              fun (y : A) ->
              typfun R ->
                fun (left : A -> A -> R) ->
                  fun (right : R) ->
                    left x y

;;

let baz = typfun A -> 
            typfun R ->
              fun (left : A -> A -> R) ->
                fun (right : R) ->
                  right

;;

let Project_bar1 = typfun A ->
                    fun (b : [[Foo A]]) ->
                      b <A> (fun (x : A) ->
                              fun (y : A) ->
                                x) x
  
;;
                      
let Project_bar2 = typfun A ->
                     fun (b : [[Foo A]]) ->
                       b <A> (fun (x : A) ->
                                fun (y : A) ->
                                  y) y

;;

let Discriminate_foo = typfun A ->
                         typfun R ->
                           fun (e1 : [[Foo A]]) ->
                             fun (e2 : R) ->
                               fun (e3 : R) ->
                                 e1 <R> (fun (x : A) -> 
                                           fun (y : A) -> e2)
                                        e3
                  
;; 


type [[Option T]] = forall R . (T -> R) -> R -> R

;;

let some = typfun T -> fun (x : T) -> typfun R -> 
             fun (some : T -> R) -> fun (none : R) -> 
               some x
               
;;

let none = typfun T -> typfun R ->
             fun (some : T -> R) -> fun (none : R) -> 
               none
               
;;

let option_case  = typfun T -> typfun R ->
                     fun (v : [[Option T]]) ->
                       fun (some_case : T -> R) ->
                         fun (none_case : R) ->
                           v <R> some_case none_case
                           
;;

type [[List T]] = forall R . (T -> R -> R) -> R -> R

;;

let cons = typfun T -> 
             fun (hd : T) ->
               fun (tl : [[List T]]) ->
                 typfun R -> 
                   fun (c : T -> R -> R) -> 
                     fun (n : R) ->
                       c hd (tl <R> c n)
                   
;;


let empty = typfun T -> 
              typfun R ->
                fun (c : T -> R -> R) ->
                  fun (n : R) ->
                    n


;;


let fold_right = typfun T ->
                   typfun B ->
                     fun (f : T -> B -> B) -> 
                       fun (lst : [[List T]]) -> 
                         fun (acc : B) ->
                           lst <B> f acc

;;


let head = typfun T ->
            fun (lst : [[List T]]) ->
              fold_right <T> <[[Option T]]> (fun (hd : T) ->
                                               fun (hdp : [[Option T]]) ->
                                                 some<T> hd) lst (none<T>)

;;

let snoc = typfun T ->
             fun (n : T) ->
               fun (lst : [[List T]]) ->
                 fold_right <T> <[[List T]]> (fun (hd : T) ->
                                                fun (lstp : [[List T]]) ->
                                                  cons<T> hd lstp) lst (cons<T> n (empty<T>))

;;

let reverse = typfun T ->
                fun (lst : [[List T]]) ->
                  fold_right <T> <[[List T]]> (fun (hd : T) ->
                                                 fun (lstp : [[List T]]) ->
                                                   snoc <T> hd lstp) lst (empty<T>)
