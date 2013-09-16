type time = Time of int * int * int

let seconds_since_midnight (hours : int) (minutes : int) (seconds : int) : int =
  ((hours * 60) + minutes) * 60 + seconds


let seconds_since_midnight2 (t : time) : int =
  match t with
    Time (hours, minutes, seconds) -> seconds_since_midnight hours minutes seconds

let t1 : time = Time (0, 0, 0)
let t2 : time = Time (23, 59, 59)

;;

print_string (string_of_int (seconds_since_midnight2 t1) ^ " " ^
              string_of_int (seconds_since_midnight2 t2) ^ "\n")

TEST "testing seconds_since_midnight2 0, 0, 0" =
  seconds_since_midnight2 t1 = 0

TEST "testing seconds_since_midnight2 23, 59, 59" =
  seconds_since_midnight2 t2 = 86399
