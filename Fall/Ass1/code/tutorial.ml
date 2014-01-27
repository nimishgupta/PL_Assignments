let rec factorial (n : int) : int =
  if n = 0 then 
    1
  else
    n * factorial (n-1)

;;


print_string ("factorial 5 = " ^ string_of_int (factorial 5) ^ "\n")


TEST "testing factorial 5" =
  factorial 5 = 120

TEST "testing factorial 8" =
  factorial 8 = 1*2*3*4*5*6*7*8
