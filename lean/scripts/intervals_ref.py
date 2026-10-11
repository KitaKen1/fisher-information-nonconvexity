"""Outward-rounded dyadic intervals and order-two jets, using integers only.

An interval (lo, hi) denotes [lo / 2**160, hi / 2**160].
Jet coefficients are (g, g', g''/2), all with respect to r.
This executable is a computer-assisted calculation, not a Lean proof.
"""
from dataclasses import dataclass
from math import factorial

BITS = 160
S = 1 << BITS


def ceildiv(a, b):
    assert b > 0
    return -((-a) // b)


def icbrt(n):
    assert n >= 0
    if n == 0:
        return 0
    x = 1 << ((n.bit_length() + 2) // 3)
    while True:
        y = (2 * x + n // (x * x)) // 3
        if y >= x:
            assert x**3 <= n < (x + 1)**3
            return x
        x = y


@dataclass(frozen=True)
class IV:
    lo: int
    hi: int

    def __post_init__(self):
        assert self.lo <= self.hi

    @staticmethod
    def rat(n, d=1):
        assert d > 0
        return IV(n * S // d, ceildiv(n * S, d))

    @staticmethod
    def cast(x):
        return x if isinstance(x, IV) else IV.rat(x)

    def __add__(self, x):
        x = IV.cast(x)
        return IV(self.lo + x.lo, self.hi + x.hi)

    __radd__ = __add__

    def __neg__(self):
        return IV(-self.hi, -self.lo)

    def __sub__(self, x):
        return self + (-IV.cast(x))

    def __rsub__(self, x):
        return IV.cast(x) + (-self)

    def __mul__(self, x):
        x = IV.cast(x)
        a = [self.lo*x.lo, self.lo*x.hi, self.hi*x.lo, self.hi*x.hi]
        return IV(min(a) // S, ceildiv(max(a), S))

    __rmul__ = __mul__

    def reciprocal(self):
        if self.hi < 0:
            return -((-self).reciprocal())
        assert self.lo > 0, 'interval division through zero'
        return IV(S*S // self.hi, ceildiv(S*S, self.lo))

    def __truediv__(self, x):
        if isinstance(x, int):
            assert x != 0
            if x < 0:
                return (-self) / (-x)
            return IV(self.lo // x, ceildiv(self.hi, x))
        return self * IV.cast(x).reciprocal()

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        if n == 0:
            return IV.rat(1)
        den = S**(n-1)
        if n % 2:
            a, b = self.lo**n, self.hi**n
        else:
            a = 0 if self.lo <= 0 <= self.hi else min(self.lo**n, self.hi**n)
            b = max(self.lo**n, self.hi**n)
        return IV(a // den, ceildiv(b, den))

    def exp(self):
        return IV(exp_point(self.lo).lo, exp_point(self.hi).hi)

    def cbrt(self):
        assert self.lo >= 0
        a, b = icbrt(self.lo*S*S), icbrt(self.hi*S*S)
        return IV(a, b if b**3 == self.hi*S*S else b+1)

    def abs_upper(self):
        return max(abs(self.lo), abs(self.hi))


def exp_point(x):
    """Enclose exp(x/S); the Taylor remainder is bounded before squaring."""
    assert 2*S < 8**33 * factorial(33)
    negative = x < 0
    x = abs(x)
    k = 0
    while 8*x > S*(1 << k):
        k += 1
    z = IV(x // (1 << k), ceildiv(x, 1 << k))
    assert 0 <= z.lo <= z.hi <= S//8
    term = total = IV.rat(1)
    for j in range(1, 33):
        term = (term*z)/j
        total = total+term
    total = IV(total.lo, total.hi+1)
    if negative:
        total = total.reciprocal()
    for _ in range(k):
        total = total**2
    return total


@dataclass(frozen=True)
class Jet:
    v: IV
    d: IV
    e: IV

    @staticmethod
    def const(x):
        return Jet(IV.cast(x), IV.rat(0), IV.rat(0))

    @staticmethod
    def cast(x):
        return x if isinstance(x, Jet) else Jet.const(x)

    def __add__(self, x):
        x = Jet.cast(x)
        return Jet(self.v+x.v, self.d+x.d, self.e+x.e)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, -self.d, -self.e)

    def __sub__(self, x):
        return self + (-Jet.cast(x))

    def __rsub__(self, x):
        return Jet.cast(x) + (-self)

    def __mul__(self, x):
        x = Jet.cast(x)
        return Jet(self.v*x.v, self.d*x.v+self.v*x.d,
                   self.e*x.v+self.d*x.d+self.v*x.e)

    __rmul__ = __mul__

    def __truediv__(self, n):
        assert isinstance(n, int) and n != 0
        return Jet(self.v/n, self.d/n, self.e/n)

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        if n == 0:
            return Jet.const(1)
        if n == 1:
            return self
        return Jet(self.v**n, n*self.v**(n-1)*self.d,
                   n*self.v**(n-1)*self.e + (n*(n-1)//2)*self.v**(n-2)*self.d**2)

    def exp(self):
        y = self.v.exp()
        return Jet(y, y*self.d, y*(self.e+self.d**2/2))

    def cbrt(self):
        y = self.v.cbrt()
        assert y.lo > 0
        return Jet(y, self.d/(3*y**2), self.e/(3*y**2)-self.d**2/(9*y**5))

    def logistic(self):
        # exp(v)/(1+exp(v)) = 1 - 1/(1+exp(v)); monotone endpoint evaluation.
        def point(a):
            z = exp_point(a)
            return 1-(1+z).reciprocal()
        y = IV(max(0, point(self.v.lo).lo), min(S, point(self.v.hi).hi))
        z = y*(1-y)
        return Jet(y, z*self.d, z*self.e+z*(1-2*y)*self.d**2/2)


def radial(r):
    """F and its r derivatives. u1,u2,u3 below are s derivatives of u."""
    s = r**2/2
    v = 15-2*s-s**2
    p = v.logistic()
    vs = -2-2*s
    u1 = 4*p*vs/3
    u2 = 4*(-2*p+p*(1-p)*vs**2)/3
    u3 = 4*(-6*p*(1-p)*vs+p*(1-p)*(1-2*p)*vs**3)/3
    a = -u1
    k = 8*s**3*u3**2 + 24*s**2*u2*u3 + 258*s*u2**2 + 2*(40*a**3+(a-2*s*u2)**3)
    y = 1+v.exp()
    return r**40 * y * y.cbrt() * k
