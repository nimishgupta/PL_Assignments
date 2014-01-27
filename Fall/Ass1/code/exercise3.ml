let rec fibonacci (n : int) : int =
  if n = 0 then 0
  else if n = 1 then 1
       else (fibonacci (n-1)) + (fibonacci (n-2))

TEST "testing fibonacci (0)" =
  fibonacci 0 = 0

TEST "testing fibonacci (1)" = 
  fibonacci 1 = 1

TEST "testing fibonacci (46)" =
  fibonacci 46 = 1836311903
