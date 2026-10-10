# A 41-Dimensional Counterexample to Convexity of Fisher Information Along the Heat Flow

The convexity problem for Fisher information along Gaussian heat flow asks the following question.

> [!NOTE]
> **Question (Convexity of Fisher information).**
>
> For every smooth positive probability density $f$ on $\mathbb R^d$, is
>
> $$
> I_f(t)=\int_{\mathbb R^d}|\nabla\log(f*\gamma_t)|^2(f*\gamma_t)\,dx
> $$
>
> convex as a function of $t>0$, whenever it is finite?

Here $\gamma_t$ is the centered Gaussian density of covariance $t\,\mathrm{Id}$, so $P_tf=f*\gamma_t$ solves $\partial_tP_tf=\tfrac12\Delta P_tf$. The question concerns ordinary convexity of $I_f$.

This repository presents a proposed computer-assisted counterexample in dimension $41$. A proof sketch follows; the [PDF manuscript](PDF/fisher_heat_nonconvexity.pdf) contains the detailed argument and the interval calculation.

## Proof sketch

### 1. Find a negative radial integral

For a positive smooth function $p$, write

$$
H_p=-\nabla^2\log p,\qquad
K_p=|\nabla H_p|_F^2+2\mathrm{tr}(H_p^3).
$$

Choose the radial logarithmic profile

$$
u(s)=\frac43\log(1+e^{15-2s-s^2}),\qquad s=|x|^2/2.
$$

The tensor contractions reduce to an explicit scalar kernel $K_{41}[u](s)$. Integer interval arithmetic on $8192$ subintervals, including a midpoint remainder bound, gives

$$
J=\int_0^8 r^{40}e^{u(r^2/2)}K_{41}[u](r^2/2)\,dr
<-7\cdot10^{18}.
$$

### 2. Cut off the bump and repeat it periodically

Let $b(a)=e^{-1/a}$ for $a>0$ and $b(a)=0$ otherwise. Define

$$
\eta(v)=\frac{b(2-v)}{b(2-v)+b(v-1)},\qquad
\widetilde u(s)=\eta(s/16)u(s).
$$

The radial bump $w(x)=\widetilde u(|x|^2/2)$ is supported in the ball of radius $8$. Set

$$
U(x)=\sum_{z\in\mathbb Z^{41}}w(x-20z),\qquad q(x)=e^{U(x)}.
$$

The supports are disjoint, so $q$ is smooth and periodic with all derivatives bounded. Explicit derivative estimates show that the cutoff changes $J$ by less than $10^{-140}$.

### 3. Retain a negative cell average

Write $\langle g\rangle=20^{-41}\int_{[-10,10]^{41}}g$ and $r_0=10^{10}/20^{41}$. Polar integration gives

$$
\langle qK_q\rangle<-6r_0,\qquad
1\leq\langle q\rangle<1+10^{-30}.
$$

The functions $q$, $qK_q$, $q\mathrm{tr}(H_q^2)$ and $q\mathrm{tr}(H_q)$ each have absolute value below $10^{28}$. These bounds control the subsequent Gaussian corrections.

### 4. Obtain a fixed probability density

Take a Gaussian envelope of standard deviation $R=10^{40}$ and normalize:

$$
Z=\int_{\mathbb R^{41}}q\gamma_{R^2}\,dx,\qquad
f=Z^{-1}q\gamma_{R^2}.
$$

Gaussian averages of the four periodic functions differ from their cell averages by less than $10^{-80}$. Since $H_f=H_q+R^{-2}\mathrm{Id}$, expanding the cubic term and bounding every correction yields

$$
D(f):=\int_{\mathbb R^{41}}fK_f\,dx<-10^{-44}.
$$

### 5. Pass to the actual heat flow

Completing the square in the Gaussian convolution gives

$$
P_tf(x)=Z^{-1}\gamma_{R^2+t}(x)
\bigl(P_{\beta_t}q\bigr)(\alpha_t x),\qquad
\alpha_t=\frac{R^2}{R^2+t},\quad
\beta_t=\frac{R^2t}{R^2+t}.
$$

This identity supplies Gaussian domination for differentiation under the integral and integration by parts. It follows that

$$
I_f''(t)=D(P_tf),\qquad D(P_tf)\longrightarrow D(f)<0
\quad(t\downarrow0).
$$

Thus $I_f''(t)<0$ for every sufficiently small positive $t$, proving the asserted failure of convexity.

## Verification

The [verification scripts](verify/) use only the Python 3 standard library. From the repository root, run:

```sh
python3 -B verify/verify_integral.py
python3 -B verify/check_constants.py
```

These commands recompute all 8192 interval cells and the 47 exact rational side checks, then regenerate the files in [certificate/](certificate/): the cell enclosures (`radial_cells.csv`), exact aggregate bounds and hashes (`result.json`), and side-check results (`constants.json`). The integral calculation starts from the formulas and does not use the saved certificate as an input.

## Detailed manuscript

- [PDF manuscript](PDF/fisher_heat_nonconvexity.pdf)

Public draft 1, 10 October 2026. Full Lean formalization remains future work.
