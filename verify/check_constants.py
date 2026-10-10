"""Exact rational side checks used by the analytic argument in the manuscript."""
import json
from fractions import Fraction as Q
from math import factorial as fac
from pathlib import Path

checks = {}


def check(name, statement):
    checks[name] = bool(statement)
    if not statement:
        raise AssertionError(name)


check('Taylor remainder < 2^-160', 2*2**160 < 8**33*fac(33))
check('elementary lower bound e > 5/2', sum(Q(1,fac(j)) for j in range(4)) > Q(5,2))
# For j >= 5, successive terms of the e-series have ratio <= 1/6.
check('elementary upper bound e < 11/4', sum(Q(1,fac(j)) for j in range(5))+Q(1,120)/(1-Q(1,6)) < Q(11,4))
check('e^2 < 8', Q(11,4)**2 < 8)
check('e^22 < 10^10', Q(11,4)**22 < 10**10)
check('e^-273 < 10^-100', Q(5,2)**273 > 10**100)
check('b prime bound', fac(2)==2)
check('b second derivative bound', fac(4)+2*fac(3)==36)
check('b third derivative bound', fac(6)+6*fac(5)+6*fac(4)==1584)
check('reciprocal derivative bound 1', 4*8**2==256)
check('reciprocal derivative bound 2', 2*4**2*8**3+72*8**2==20992)
check('reciprocal derivative bound 3', 6*4**3*8**4+6*4*72*8**3+3168*8**2==2660352)
check('eta prime', 2*8+256==272<300)
check('eta second derivative', 36*8+2*2*256+20992==22304<30000)
check('eta third derivative', 1584*8+3*36*256+3*2*20992+2660352==2826624<3000000)
check('chi prime', Q(300,16)<20)
check('chi second derivative', Q(30000,16**2)<120)
check('chi third derivative', Q(3000000,16**3)<750)
check('u prime tail', Q(4,3)*66<100)
check('u second tail', Q(4,3)*(2+66**2)<6000)
check('u third tail', Q(4,3)*(6*66+66**3)<400000)
check('cutoff first tail', 100+20*2<10**6)
check('cutoff second tail', 6000+2*20*100+120*2<10**6)
check('cutoff third tail', 400000+3*20*6000+3*120*100+750*2<10**6)
check('tail quadratic coefficient', 8*32**3+24*32**2+258*32==294976)
check('tail cubic coefficient', 2*(40+65**3)==549330)
check('tail kernel bound', 294976+549330<10**6)
check('tail M < 1', Q(10**6,10**100)<1)
check('tail weights < 2 via exp(x) <= 1/(1-x)', 1/(1-Q(2,10**100))<2)
check('8^41 < 10^38', 8**41<10**38)
check('cutoff error < 10^-140', Q(4*10**18*8**41,10**200)<Q(1,10**140))
check('global u bound', Q(4,3)*(15+1)<22)
check('global u prime', Q(4,3)*66<100)
check('global u second', Q(4,3)*(2+Q(66**2,4))<1500)
check('global u third', Q(4,3)*(Q(6*66,4)+Q(66**3,4))<10**5)
check('radial eigenvalue bound', 100+64*1500==96100)
kbound=8*32**3*10**10+24*32**2*1500*10**5+258*32*1500**2+2*(40*100**3+96100**3)
check('global K bound', kbound==4400152418000000<10**16)
check('four periodic functions bounded by 10^28', max(1,kbound,40*100**2+96100**2,40*100+96100)*10**10<10**28)
check('sphere area > 10^-8 using pi > 3', Q(2**41*fac(20)*3**20,fac(40))>Q(1,10**8))
mass = Q(8,3)*4**20*(Q(11,4)**15+Q(11,4)**20)/20**41
check('excess average mass < 10^-30', mass<Q(1,10**30))
check('A > 1000 using pi > 3', Q(2*9*10**80,20**2)>1000)
check('2^1000 > 10^300', 2**1000>10**300)
check('binomial comparison', Q(251,250)**40<2)
check('Gaussian averaging error < 10^-80', Q(328*10**28,10**300)<Q(1,10**80))
check('normalizer < 2', 1+Q(1,10**30)+Q(1,10**80)<2)
r0 = Q(10**10,20**41)
correction = Q(1,10**80)+Q(6*10**28,10**80)+Q(6*10**28,10**160)+Q(164,10**240)
check('Gaussian corrections < r0', correction<r0)
check('final D < -10^-44', Q(5,2)*r0>Q(1,10**44))
result = {'checks':checks,'passed':len(checks),'scope':'Rational comparisons only; analytic identities are proved in the manuscript.'}
dest = Path(__file__).resolve().parents[1]/'certificate'/'constants.json'
dest.parent.mkdir(exist_ok=True)
dest.write_text(json.dumps(result,indent=2)+'\n')
print(f'PASS: {len(checks)} exact rational comparisons')
