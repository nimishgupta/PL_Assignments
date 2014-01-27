type time = Time of int * int * int

let seconds_since_midnight (hours : int) (minutes : int) (seconds : int) : int =
  ((hours * 60) + minutes) * 60 + seconds

let seconds_since_midnight2 (t : time) : int =
  match t with
    Time (hours, minutes, seconds) -> seconds_since_midnight hours minutes seconds


let time_diff (t1 : time) (t2 : time) : int =
  let t1_secs : int = seconds_since_midnight2 t1 in
    let t2_secs : int = seconds_since_midnight2 t2 in
      abs (t2_secs - t1_secs)

;;

print_string (string_of_int (time_diff (Time (23, 59, 59)) (Time (0, 0, 0))) ^ "\n")

TEST = time_diff (Time (23, 59, 59)) (Time (23, 59, 59)) = 0
TEST = time_diff (Time (23, 59, 58)) (Time (23, 59, 59)) = 1
TEST = time_diff (Time (23, 59, 59)) (Time (23, 59, 58)) = 1
TEST = time_diff (Time (23, 59, 59)) (Time (0, 0, 0))    = 86399

