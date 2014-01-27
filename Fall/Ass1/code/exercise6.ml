type time = Time of int * int * int

let seconds_to_time (seconds : int) : time =
  let hours : int = seconds/3600 in
    let minutes : int = (seconds - hours * 3600)/60 in
      let secs : int = seconds mod 60 in
        Time (hours, minutes, secs)


TEST = seconds_to_time 0 = Time (0, 0, 0)
TEST = seconds_to_time 86399 = Time (23, 59, 59)
TEST = seconds_to_time 86400 = Time (24, 0, 0)
