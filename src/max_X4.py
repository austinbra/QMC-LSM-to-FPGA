import numpy as np

S0 = 144 #initial stock price
vol = .5 # 50% volatility
r = .1 #risk free rate
T = 1/12 #time period daily monthly etc.

sMax = S0 * np.exp((r + (2*vol))*T)
N = 100000 #worst case N
#n copies of sMax
x = np.full(N, sMax)
sum4 = np.sum(x**4)
print("S max = ", sMax)
print("sum X^4 = ", f"{sum4:.5e}")
print("required bits: ", np.ceil(np.log2(sum4)))