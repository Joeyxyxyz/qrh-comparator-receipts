import math
def leggauss(n):
    xs=[];ws=[]
    for i in range(1,n+1):
        x=math.cos(math.pi*(i-0.25)/(n+0.5))
        for _ in range(100):
            p0=1.0;p1=x
            for k in range(2,n+1):
                p0,p1=p1,((2*k-1)*x*p1-(k-1)*p0)/k
            dp=n*(x*p1-p0)/(x*x-1)
            dx=p1/dp
            x-=dx
            if abs(dx)<1e-15: break
        p0=1.0;p1=x
        for k in range(2,n+1):
            p0,p1=p1,((2*k-1)*x*p1-(k-1)*p0)/k
        dp=n*(x*p1-p0)/(x*x-1)
        xs.append(x);ws.append(2/((1-x*x)*dp*dp))
    return xs,ws
def det(A):
    n=len(A);A=[r[:] for r in A];d=1.0
    for i in range(n):
        p=max(range(i,n),key=lambda r:abs(A[r][i]))
        if abs(A[p][i])<1e-300: return 0.0
        if p!=i: A[i],A[p]=A[p],A[i]; d=-d
        d*=A[i][i]
        for r in range(i+1,n):
            f=A[r][i]/A[i][i]
            if f:
                for c in range(i,n): A[r][c]-=f*A[i][c]
    return d
def sinc(u):
    return 1.0 if abs(u)<1e-14 else math.sin(math.pi*u)/(math.pi*u)
GX,GW=leggauss(30)
def E0(s):
    if s==0: return 1.0
    x=[0.5*s*(t+1) for t in GX]; w=[0.5*s*t for t in GW]
    m=len(x)
    A=[[(1.0 if i==j else 0.0)-math.sqrt(w[i]*w[j])*sinc(x[i]-x[j]) for j in range(m)] for i in range(m)]
    return det(A)
QX,QW=leggauss(120)
L=6.0
m2=0.0;m1=0.0
for t,wt in zip(QX,QW):
    s=0.5*L*(t+1); w=0.5*L*wt
    e=E0(s)
    m2+=2*w*e
print("E(0;1) =",E0(1.0))
print("second moment",m2,"variance",m2-1,"sd",math.sqrt(m2-1))
print("surmise sd",math.sqrt(3*math.pi/8-1))
