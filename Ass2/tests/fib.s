let make_fib = lambda (self, n) . if 0 == n || 1 == n then n else self(self, n - 1) + self(self, n - 2) in
let fib = lambda (n) . make_fib (make_fib, n) in fib(10)
