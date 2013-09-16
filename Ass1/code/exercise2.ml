let seconds_since_midnight (hours : int) (minutes : int) (seconds : int) : int =
  ((hours * 60) + minutes) * 60 + seconds

TEST "testing function seconds_since_midnight 0, 0 ,0" =
  seconds_since_midnight 0 0 0 = 0

TEST "testing function seconds_since_midnight 23, 59, 59" =
  seconds_since_midnight 23 59 59 = 86399
