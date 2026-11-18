"""Direct Arb energy and scope checks, independent of I2 and arbcert.
Input angles are exact binary64 JSON numbers. Outputs are certified interval calculations.
"""
import json
from flint import arb, ctx
ctx.prec = 256
cfg = json.load(open('cx_config.json'))
N = cfg['N']
z = [arb(x) for x in cfg['z']]
T = arb(1)/40
vp = 1/(2*arb.pi()*T)
K = lambda k: 8*vp*vp/(vp*vp+k*k)
def spins(a, p):
    return [(a[i].sin()*p[i].cos(), a[i].sin()*p[i].sin(), a[i].cos()) for i in range(N)]
x = spins(z[:N], z[N:2*N])
y = spins(z[2*N:3*N], z[3*N:])
dot = lambda a,b: sum((a[k]*b[k] for k in range(3)), arb(0))
ze = sum(((2*n+1)*(2-x[n][2]-y[n][2]) for n in range(N)), arb(0))
ext = sum((sum((K(k) for k in range(N-n,N+n+1)),arb(0))*(2-x[n][2]-y[n][2]) for n in range(N)),arb(0))
same = sum((K(m-n)*(2-dot(x[n],x[m])-dot(y[n],y[m])) for n in range(N) for m in range(n+1,N)),arb(0))
cross = -sum((K(n+m+1)*(1+x[n][0]*y[m][0]+x[n][1]*y[m][1]-x[n][2]*y[m][2]) for n in range(N) for m in range(N)),arb(0))
base = ze+ext+same+cross
out = {'method':'256-bit Arb direct pair sum; exterior telescoped exactly','energies':{},'positive_frequency_z':[]}
for label,nc in [('fixed_index_5',5),('omega_c_5',32),('omega_c_10',64)]:
    if label.startswith('omega_c'):
        cutoff = arb(int(label.rsplit('_',1)[1]))
        assert ((2*nc-1)*arb.pi()*T < cutoff) and (cutoff < (2*nc+1)*arb.pi()*T)
    coul = 10*sum((sum((x[n][d]+y[n][d] for n in range(min(nc,N))),arb(0))**2 for d in range(2)),arb(0))
    E = base+coul
    assert (E<0) if nc==5 else (E>0)
    out['energies'][label] = E.str(65)
    print(label, 'Nc=',nc,'E=',E.str(20))
for n in range(N):
    out['positive_frequency_z'].append(x[n][2].str(16))
    assert (x[n][2]<0) if n<6 else (x[n][2]>0)
print('positive-frequency reversed z sites: exactly n=0,...,5')
print('first eight z:',out['positive_frequency_z'][:8])
cutoff = 2*arb.pi()*T*5
out['representative_cutoff_T1'] = cutoff.str(20)
print('representative omega_c(T1)=',cutoff.str(20))
# Conservative separation value used in the manuscript, with a strict Arb comparison.
L_bound = arb('79.873')
delta = (arb(1)/2/(2*L_bound)).sqrt()
assert delta>arb('0.0559')
out['conservative_radius'] = delta.str(20)
json.dump(out,open('scope_values.json','w'),indent=2)
