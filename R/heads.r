library(Rmpfr)
pdf(file = "wofp.pdf", width=6, height=6)

p = (1:9) * 0.1
nFin = 100
precBits = 128

compute = FALSE

# compute w_n using the Bellman equation
compute_w <- function(p, nFin, precBits) {
  p = mpfr(as.character(p), precBits)
  w = mpfr(0, precBits) * (1:nFin)
  w[1] = p

  # decisionMatrix[n,n-j] = i (with i >= j) means that it is optimal to
  # throw i coins in the next round when there are n-j out of n coins with
  # head, i.e. j coins with tail

  decisionMatrix = matrix(0, nrow = nFin, ncol = nFin)

  # The next line is not necessary but true
  for(n in 1:nFin) decisionMatrix[n,n] = 0

  for(n in 2:nFin) {
    w[n] = p^n
    for(j in 1:(n-1)) {
      decisionMatrix[n,n-j] = j-1 + which.max(w[j:(n-1)])
      w[n] = w[n] + choose(n,j) * p^(n-j) * (1-p)^j * max(w[j:(n-1)])
    }
  }
  res = list(w = w, decisionMatrix = decisionMatrix)
  res
}

if(compute) {
  w = matrix(0, nrow = length(p), ncol = nFin)
  for(i in 1:length(p)) {
    res = compute_w(p[i], nFin, precBits)
    w[i,] = formatDec(res$w)
  }
}

pdf(file = "wofp1.pdf", width=6, height=6)
plot(c(1,nFin), c(0,1), type='n', xlab = "n", ylab = expression(paste(w[n])))

for(i in 1:(length(p))) {
  cat(i, "\n")
  wloc = as.numeric(w[i,])
  points(1:nFin, wloc, pch=20)
  for(j in 1:(nFin-1)) {
#    cat(j)
    cat(i, "\t", j, "\t", wloc[j], "\n")
    if(wloc[j] < wloc[j+1]) {
      lines(c(j,j+1), c(wloc[j], wloc[j+1]), col="blue")
    } else {
#      cat(i, "\t", j, "\t", wloc[j], "\n")
#      cat("else")
      lines(c(j,j+1), c(wloc[j], wloc[j+1]), col="red")
    }
  }
}

dev.off()


# plot w3 and w4 depending on p
p = seq(0.01, 0.5, by = 0.01)
nFin=6

w1 = w2 = matrix(0, nrow = length(p), ncol = nFin)
for(i in 1:length(p)) {
  res = compute_w(p[i], nFin, precBits)
  w1[i,] = formatDec(res$w)
}

pdf(file = "wofp2.pdf", width=6, height=6)
plot(c(0,.5), c(0,.5), type='n', xlab = "n", ylab = expression(paste(w[n])))
for(i in 1:nFin) {
  wloc = as.numeric(w1[,i])
  lines(p, wloc)
}
dev.off()

# w3 - w4
pdf(file = "wofp3.pdf", width=6, height=6)
plot(c(0,.5), c(0,.1), type='n', xlab = "p", ylab = expression(paste(w[3], "-", w[4])))
delta = as.numeric(w1[,3]) - as.numeric(w1[,4])
lines(p, delta)
w2 = p^3*(1-p)^2 + 3*p^3*(1-p)^4 + 3*p^3*(1-p)^5 + 6 * p^3*(1-p)^7 - p^4*(1-p)^3 - 3*p^4*(1-p)^4 - 3*p^4*(1-p)^5 - 6 * p^4*(1-p)^6 - 3 * p^4 * (1-p)^3 - 3 * p^4 * (1-p)^5 - 12 * p^4 * (1-p)^6 
lines(p, w2)
dev.off()


