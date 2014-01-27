let make_length_list = lambda (self, l). if empty? (l) then 0 else 1 + self (self, tail (l)) in
  let length_list = lambda (l) . make_length_list (make_length_list, l) in length_list(1::2::3::4::5::6::7::8::empty)
