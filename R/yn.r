N = 30
p = 0.2

v = 0*(1:N)
v0 = 1
v[1] = p
for(n in 2:N) {
  v[n] = v[n-1] * (1 + p*(1-p)^(n-1)) - (1-p)^2*p^(n-1)
  if(n > 2) {
    for(j in 1:(n-2)) {
      v[n] = v[n] + choose(n-1,j)*p^(n-1-j)*(1-p)^(j+1) * (v[j+1] - v[j])
    }
  }	
}
cat("v = ", v, "\n")

y = 0*(1:N)
y[1] = 0
y[2] = p*(1-p)
for(n in 3:N) {
  for(j in 2:(n-1)) {
    y[n] = y[n]  + p*(1-p)^(n-1)*y[j]  #  + choose(n-1,j-1)*p^(n-j)*(1-p)^j * y[j] 
    if(j < n-1) {
      y[n] = y[n] - p^(n-j)*(1-p)^(j)
    }
  }
}

vp = v
for(n in 2:N) {
  vp[n] = p - (1-2*p)*sum(y[2:n])
}
cat("vp= ", vp, "\n")
cat("y= ", y, "\n")

