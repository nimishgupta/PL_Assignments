type time = Time of int * int * int

let seconds_since_midnight (hours : int) (minutes : int) (seconds : int) : int =
  ((hours * 60) + minutes) * 60 + seconds

let seconds_since_midnight2 (t : time) : int =
  match t with
    Time (hours, minutes, seconds) -> seconds_since_midnight hours minutes seconds

let seconds_to_time (seconds : int) : time =
  let hours : int = seconds/3600 in
    let minutes : int = (seconds - hours * 3600)/60 in
      let secs : int = seconds mod 60 in
        Time (hours, minutes, secs)


let tick (t : time) : time =
  let t_secs : int = seconds_since_midnight2 t in
    seconds_to_time (t_secs + 1)

;;

print_string (string_of_int (seconds_since_midnight2 (tick (Time (23, 59, 58)))) ^ "\n")

TEST = tick (Time (0, 0, 0))    = Time (0, 0, 1)
TEST = tick (Time (23, 59, 58)) = Time (23, 59, 59)
