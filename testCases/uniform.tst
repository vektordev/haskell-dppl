backends: interpreter, julia, python, batched
p(0.5)=(1.0,1.0,False)
p(-0.5)=(0.0,1.0,True)
p(2.0)=(0.0,1.0,True)
cdf(0.3)=(0.3, 0.0)
cdf(0.0)=(0.0, 0.0)
cdf(1.1)=(1.0, 0.0)