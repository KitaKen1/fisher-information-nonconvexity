"""Recompute every cell and certify the real integral by a midpoint remainder.

Run from any directory: python3 verify/verify_integral.py
Uses only the Python standard library, and never reads certificate values as input.
"""
import argparse
import csv
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from time import monotonic
from intervals import IV, Jet, S, BITS, radial


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=8192)
    ap.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'certificate')
    args = ap.parse_args()
    n = args.n
    assert n > 0
    args.output.mkdir(parents=True, exist_ok=True)
    lo = hi = err = 0
    started = monotonic()
    csvpath = args.output/'radial_cells.csv'
    with csvpath.open('w', newline='') as stream:
        writer = csv.writer(stream, lineterminator='\n')
        writer.writerow(['cell','midpoint_lower_scaled','midpoint_upper_scaled','abs_half_second_derivative_upper_scaled'])
        for j in range(n):
            left, right = IV.rat(8*j,n), IV.rat(8*(j+1),n)
            interval = IV(left.lo,right.hi)
            m = IV.rat(4*(2*j+1), n)
            mid = radial(Jet.const(m)).v
            bound = radial(Jet(interval,IV.rat(1),IV.rat(0))).e.abs_upper()
            lo += mid.lo; hi += mid.hi; err += bound
            writer.writerow([j,mid.lo,mid.hi,bound])
            if (j+1) % 1024 == 0:
                print(f'{j+1}/{n} cells', flush=True)
    h = Fraction(8,n)
    lower, upper, error = h*lo/S, h*hi/S, h**3*err/(12*S)
    bounds = [lower-error,upper+error]
    floor = lambda x: x.numerator//x.denominator
    ceil = lambda x: -((-x.numerator)//x.denominator)
    data = {
        'description':'New reconstruction from the supplied mathematical formulas; not the original verifier.',
        'bits':BITS,'cells':n,'domain':[0,8],
        'midpoint_lower_floor':floor(lower),'midpoint_upper_ceil':ceil(upper),
        'remainder_upper_ceil':ceil(error),
        'integral_lower_floor':floor(bounds[0]),'integral_upper_ceil':ceil(bounds[1]),
        'integral_upper_below_minus_7e18':bounds[1]<-7*10**18,
        'exact_lower':{'num':bounds[0].numerator,'den':bounds[0].denominator},
        'exact_upper':{'num':bounds[1].numerator,'den':bounds[1].denominator},
        'sum_midpoint_lower_scaled':lo,'sum_midpoint_upper_scaled':hi,'sum_error_scaled':err,
        'csv_sha256':hashlib.sha256(csvpath.read_bytes()).hexdigest(),
        'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(__file__).with_name('intervals.py')]},
    }
    (args.output/'result.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k in ['cells','bits','midpoint_lower_floor','midpoint_upper_ceil','remainder_upper_ceil','integral_lower_floor','integral_upper_ceil','integral_upper_below_minus_7e18']},indent=2))
    print(f'Elapsed: {monotonic()-started:.1f}s')
    if not data['integral_upper_below_minus_7e18']:
        raise SystemExit('Insufficient enclosure: the claimed negative bound was not certified.')


if __name__ == '__main__':
    main()
