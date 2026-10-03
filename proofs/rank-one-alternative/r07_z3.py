# psi(nu) = i phi'(nu) = -(i/pi) log(1 - exp(-i pi nu)):  check psi(S) in S, psi^3 = id, nu + psi + psi^2 = 1 + i c
import mpmath as mp
mp.mp.dps = 40
psi = lambda z: -(1j/mp.pi)*mp.log(1 - mp.exp(-1j*mp.pi*z))
import random
random.seed(1)
for _ in range(6):
    z = mp.mpc(random.uniform(0.01,0.99), random.uniform(-4,4))
    z1 = psi(z); z2 = psi(z1); z3 = psi(z2)
    print(mp.nstr(z,8), ' psi^3-id =', mp.nstr(abs(z3-z),3), '  sum =', mp.nstr(z+z1+z2, 20))
# fixed point
f = mp.findroot(lambda z: psi(z)-z, mp.mpc(1/3., 0.2))
print('fixed point', f, ' 3*Im =', 3*f.imag, '  check', mp.nstr(abs(psi(f)-f),3))
