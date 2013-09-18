let make_fac = lambda (self, n) . if0 n then 1 else n * self(self, n - 1) in
let fac = lambda (n) . make_fac(make_fac, n) in fac(5)

