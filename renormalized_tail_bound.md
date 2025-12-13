### Quantitative renormalized-tail BMO bound: why (A′)/(B′) as stated cannot hold (and what *is* provable)

#### Setup (as in the task)
- Let \(\xi(s)\) be the completed Riemann zeta function

\[\xi(s) := \tfrac12 s(s-1)\,\pi^{-s/2}\,\Gamma(s/2)\,\zeta(s),\]

  so \(\xi\) is entire of order 1, satisfies \(\xi(s)=\xi(1-s)\), and its zeros \(\rho=\beta+i\gamma\) lie in \(0<\beta<1\).
- Write upper-half-plane coordinates centered at \(\Re(s)=1/2\): for a zero \(\rho=\beta+i\gamma\) with \(\beta>1/2\), set

\[\sigma_\rho := \beta-\tfrac12 \in (0,\tfrac12),\qquad \gamma_\rho := \gamma.\]

- For a “Whitney interval” \(I=(t_0,L)\) with \(L>0\), define \(I_R=[t_0-L,t_0+L]\) and \(|I|=2L\), and the annuli \(A_0,A_1,\dots,A_K\) and \(B(I,K)=\bigcup_{j=0}^K A_j\) exactly as in the prompt.
- Define the boundary “renormalized tail” function

\[f_{\mathrm{tail}}^I(t)
:= \log|\xi(\tfrac12+it)| - \tfrac12\sum_{\rho\in B(I,K)}\log\big((t-\gamma_\rho)^2+\sigma_\rho^2\big).\]

- BMO on \(I_R\) is the usual

\[\|f\|_{\mathrm{BMO}(I_R)} := \sup_{J\subseteq I_R} \frac1{|J|}\int_J \big|f(t)-\mathrm{avg}_J f\big|\,dt,\]

  where \(J=[a,b]\subseteq I_R\).

---

## 1) A hard obstruction: (A′) is **false** as stated

### Lemma 1 (the subtraction is identically empty for large \(L\))
If \(L>\tfrac23\), then for *any* center \(t_0\) and any \(K\ge 0\),

\[B(I,K)=\varnothing.\]

**Reason.** Every nontrivial zeta zero satisfies \(0<\beta<1\), hence every \(\sigma_\rho=\beta-1/2\) with \(\beta>1/2\) lies in \((0,1/2)\). But
\(A_0\) requires \(\sigma_\rho\in[0.75L,1.5L]\), and if \(L>2/3\) then \(0.75L>1/2\), so \(A_0\) is empty; the dyadic \(A_j\) have even larger \(\sigma\)-lower-bounds.

So, for example, for \(L=1\) one has \(B(I,3)=\varnothing\) and therefore

\[f_{\mathrm{tail}}^I(t)=\log|\xi(\tfrac12+it)|\quad\text{on }I_R.\]

### Lemma 2 (exact BMO constant for a logarithmic singularity)
Let \(g(t)=\log|t|\). Then on \([-1,1]\),

\[\mathrm{meanOsc}(g;-1,1)=\frac{2}{e}\approx 0.73575888.\]

**Computation.** \(\mathrm{avg}_{[-1,1]}\log|t| = \int_0^1\log t\,dt = -1\). Hence

\[\frac1{2}\int_{-1}^1|\log|t|+1|\,dt=\int_0^1|\log t+1|\,dt.
\]
Split at \(t=e^{-1}\) where \(\log t+1=0\). Since \(\int (\log t+1)dt=t\log t\),

\[\int_0^{e^{-1}}-(\log t+1)dt + \int_{e^{-1}}^1(\log t+1)dt
= -[t\log t]_0^{e^{-1}} + [t\log t]_{e^{-1}}^1
= e^{-1}+e^{-1}=\frac{2}{e}.
\]

### Lemma 3 (local lower bound near any boundary zero)
Let \(F\) be holomorphic near \(t=t_*\) and suppose \(F(t_*)=0\) with multiplicity \(m\ge 1\). Then

\[\sup_{\varepsilon>0}\ \|\log|F(\cdot)|\|_{\mathrm{BMO}([t_* -\varepsilon,\, t_*+\varepsilon])} \ge m\cdot \frac{2}{e}.
\]

**Reason.** Factor locally \(F(t)=(t-t_*)^m G(t)\) with \(G\) holomorphic and nonvanishing near \(t_*\). Then
\(\log|F(t)| = m\log|t-t_*| + \log|G(t)|\).
The second term is continuous, so its mean oscillation on \([t_* -\varepsilon, t_*+\varepsilon]\) tends to 0 as \(\varepsilon\to0\), while \(m\log|t-t_*|\) has scale-invariant mean oscillation \(m\cdot 2/e\) (by Lemma 2).

### Theorem 4 (A′ fails; in fact the supremum is \(\ge 2/e\))
Hardy’s theorem (1914) states that \(\zeta(1/2+it)\) has infinitely many zeros on the critical line. Equivalently, there exists \(t_*\in\mathbb R\) with \(\xi(1/2+it_*)=0\).

Take the Whitney interval \(I=(t_*,1)\). By Lemma 1, \(B(I,3)=\varnothing\), so
\(f_{\mathrm{tail}}^I(t)=\log|\xi(1/2+it)|\) on \(I_R=[t_*-1,t_*+1]\).
By Lemma 3 (with \(F(t)=\xi(1/2+it)\) and \(m\ge 1\)), the BMO norm of \(f_{\mathrm{tail}}^I\) on \(I_R\) is at least \(2/e\approx0.7357\), hence certainly not \(\le 0.20\).

**Conclusion:** the uniform bound demanded in (A′) cannot be proven because it is **not true** under the given definitions.

> In particular, (A′) fails even if the Riemann Hypothesis holds (then the subtraction term is empty for *all* \(I\), and the critical-line zeros still force a \(\ge 2/e\) local BMO lower bound).

---

## 2) Why (B′) does not rescue (A′) (and what the closest correct substitute looks like)

### 2.1. Even if \(\mu\) were Carleson, (A′) still fails
The measure in (B′)

\[\mu := \sum_{\rho:\,\beta>1/2} \sigma_\rho\,\delta_{(\gamma_\rho,\sigma_\rho)}\]

only “sees” zeros strictly to the right of \(\Re(s)=1/2\). But the obstruction in §1 comes from **boundary zeros** with \(\beta=1/2\), which do not appear in \(\mu\) and are not subtracted by \(B(I,3)\).
So no Carleson packing statement about \(\mu\) can imply a uniform small-BMO bound for \(f_{\mathrm{tail}}^I\) as currently defined.

### 2.2. The missing “sum over zeros” step (explicit)
A standard way to control a weighted sum \(\sum \sigma_\rho\) is the layer-cake identity:

\[\sum_{\rho\in\mathcal R} \sigma_\rho
= \sum_{\rho\in\mathcal R}\int_0^{\sigma_\rho} du
= \int_0^{\infty} \#\{\rho\in\mathcal R:\ \sigma_\rho>u\}\,du.
\]

Applied to a Carleson box restriction (e.g. \(\mathcal R=\{\rho:\ (\gamma_\rho,\sigma_\rho)\in Q_\alpha(I)\}\)), the upper limit becomes \(u\le \alpha|I|\), giving an explicit reduction of the weighted sum to (unweighted) zero counts in vertical strips.

This is exactly the kind of “legitimate control of the SUM” that is missing if one only bounds each Poisson kernel individually.

### 2.3. What (B′) would actually imply (strong local zero-density)
If (B′) held with constant \(K\), then for any \(\eta>0\), every zero in \(Q_2(I)\) with \(\sigma_\rho\ge \eta\) contributes at least \(\eta\) to \(\mu(Q_2(I))\). Hence

\[\#\{\rho:\ (\gamma_\rho,\sigma_\rho)\in Q_2(I),\ \sigma_\rho\ge\eta\}
\le \frac{\mu(Q_2(I))}{\eta}
\le \frac{K}{\eta}\,|I|.
\]

So (B′) would force a **uniform-in-height** local density bound for zeros with \(\beta\ge 1/2+\eta\) in *every* interval of length \(|I|\). This is far stronger than any unconditional theorem currently available: known zero-density estimates are global-in-\(T\) and do not rule out strong local clustering.

### 2.4. Closest unconditional substitute for (B′): a log-height dependent “Carleson” bound
Unconditionally one can only prove bounds that grow with height. A simple, explicit (but weak) statement is:

- Using \(\sigma_\rho\le 1/2\),

\[\mu(Q_2(I))\le \tfrac12\,\#\{\rho:\ |\gamma- t_0|\le L\},\]

  i.e. off-line zeros are bounded by the total zero count in that window.

- By the Riemann–von Mangoldt formula with explicit error terms (e.g. Trudgian, *Math. Comp.* (2012), Theorem 1 and Corollary 1 in `arXiv:1208.5846`), one has an explicit approximation for

\[N(T):=\#\{\rho:\ 0<\gamma\le T\}
= \frac{T}{2\pi}\log\frac{T}{2\pi e}+\frac78+S(T)+O(1/T),\]

  and an explicit bound

\[|S(T)|\le 0.111\log T+0.275\log\log T+2.450\qquad(T\ge e).\]

From this one gets, for \(t_0\) large and \(L\ge 1\), a *provable* local bound of the shape

\[\mu(Q_2(I)) \ \lesssim\  |I|\,\log(|t_0|+|I|),\]

with fully explicit constants obtainable by a direct difference estimate on \(N(t_0+L)-N(t_0-L)\).

**Scaling consequence:** any BMO/Carleson constant derived from this grows at least like \(\log |t_0|\), so it cannot yield a uniform numerical bound like 0.20.

### 2.5. A fully explicit (auditable) log-height Carleson-box bound from Rosser–Schoenfeld

This fills in the “missing **sum over zeros**” step with a standard, unconditional zero-counting input.

#### Input (explicit zero-counting approximation)

Let \(N(T)\) be the number of nontrivial zeros \(\rho=\beta+i\gamma\) of \(\zeta\) with \(0<\gamma\le T\), counted with multiplicity. Define

\[
F(T):=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+\frac78.
\]

Rosser–Schoenfeld (1962) give an explicit error term of the form

\[
\big|N(T)-F(T)\big|\le R(T):=0.137\log T+0.443\log\log T+1.588\qquad(T\ge 2).
\]

(Later work improves constants, but this is already enough to make everything explicit.)

#### Step A: explicit short-interval bound for zero counts

Fix \(T\ge 3\) and \(H\ge 1\). Then (using \(N(T+H)\le F(T+H)+R(T+H)\) and \(N(T-H)\ge F(T-H)-R(T-H)\))

\[
N(T+H)-N(T-H)\le \big(F(T+H)-F(T-H)\big)+R(T+H)+R(T-H).
\]

Since \(F'(u)=\frac{1}{2\pi}\log\frac{u}{2\pi}\) is increasing for \(u\ge 2\pi\), we have the crude bound

\[
F(T+H)-F(T-H)=\int_{T-H}^{T+H}F'(u)\,du\le 2H\,F'(T+H)\le \frac{H}{\pi}\log(T+H).
\]

Also \(R\) is increasing for \(T\ge 3\), so \(R(T+H)+R(T-H)\le 2R(T+H)\). Combining yields the fully explicit window bound

\[
N(T+H)-N(T-H)\ \le\ \frac{H}{\pi}\log(T+H)\ +\ 0.274\log(T+H)\ +\ 0.886\log\log(T+H)\ +\ 3.176.
\tag{\*\*}
\]

#### Step B: explicit Carleson-box bound for the weighted off-line measure \(\mu\)

Recall \(\mu:=\sum_{\rho:\beta>1/2}\sigma_\rho\,\delta_{(\gamma_\rho,\sigma_\rho)}\) with \(\sigma_\rho=\beta-1/2\in(0,1/2)\).
For a Whitney interval \(I=(t_0,L)\) with \(|I|=2L\), the Carleson box \(Q_2(I)\) consists of points \((t,\sigma)\) with
\(t\in[t_0-L,t_0+L]\) and \(0<\sigma\le 4L\). Hence every \(\rho\) counted by \(\mu(Q_2(I))\) satisfies
\(\gamma_\rho\in[t_0-L,t_0+L]\) and \(\sigma_\rho\le\min(4L,1/2)\), so

\[
\mu(Q_2(I))=\sum_{\rho\in Q_2(I)}\sigma_\rho\ \le\ \min(4L,1/2)\cdot \#\{\rho:\gamma_\rho\in[t_0-L,t_0+L]\}.
\]

Now let \(U:=\max(3,|t_0|+L)\) and apply (\*\*) with \(T:=U\) and \(H:=L\) (bounding the number of ordinates in the window by a short-interval count at comparable height). This gives an explicit bound

\[
\#\{\rho:\gamma_\rho\in[t_0-L,t_0+L]\}
\ \le\ \frac{L}{\pi}\log(U)\ +\ 0.274\log(U)\ +\ 0.886\log\log(U)\ +\ 3.176.
\]

Finally, divide by \(|I|=2L\) and use \(\min(4L,1/2)/(2L)=\min(2,1/(4L))\le 2\) to get a uniform (in \(L\)) Carleson-type estimate:

\[
\frac{\mu(Q_2(I))}{|I|}
\ \le\ \Big(\frac{1}{4\pi}+0.548\Big)\log(U)\ +\ 1.772\log\log(U)\ +\ 6.352.
\]

Equivalently,

\[
\mu(Q_2(I))
\ \le\ \Big(0.628\,\log(U)\ +\ 1.772\,\log\log(U)\ +\ 6.352\Big)\,|I|.
\tag{RS-Carleson(U)}
\]

This is unconditional, fully explicit, and it addresses the “sum over zeros” step transparently. The unavoidable drawback is the \(\log(U)\) growth, which prevents any uniform-in-height small constant.

---

## 3) Takeaway: what must be changed for a true “small tail BMO” lemma

To make a statement like (A′) plausible/true, one must remove the two mechanisms that force a \(\ge 2/e\) BMO lower bound:

- **boundary zeros** (critical-line zeros \(\beta=1/2\)), which create unavoidable logarithmic singularities at arbitrary small scales if they are not renormalized out, and
- **global deterministic trends** (e.g. from the \(\Gamma\)-factor inside \(\xi\)) if one allows arbitrarily large Whitney scales.

Concretely, typical fixes are:
- renormalize by subtracting *all* zeros in the Carleson box down to \(\sigma=0\) (or a mollified \(\sigma\approx 0\) version), not only \(\sigma\ge 0.75L\), and/or
- work with a one-scale oscillation norm (only subintervals \(J\) with \(|J|\simeq |I|\)), and/or
- restrict the class of Whitney intervals (e.g. \(L\le L_\mathrm{max}\)) so that global trends cannot dominate.

---

## 4) Alternative “escape hatch” target suggested by `CPM.tex`: boundary wedge for a normalized ratio \(\mathcal J\)

The analysis above shows the specific (A′)/(B′) formulation is obstructed for \(\log|\xi|\) with the given renormalization.
However, there is a different *structural* route hinted by `CPM.tex` (Section “Riemann Hypothesis Instantiation (Boundary Certificate)”):

### 4.1. Replace \(\log|\xi|\) by a **boundary-unimodular normalized ratio**

Work in the half-plane \(\Omega=\{\Re s>1/2\}\). Seek an analytic (or holomorphic) function \(\mathcal J\) on \(\Omega\) such that

\[
|\mathcal J(1/2+it)| = 1 \quad\text{for a.e. }t\in\mathbb R,
\]

and define its boundary phase
\[
w(t):=\Arg \mathcal J(1/2+it)\in(-\pi,\pi]\quad\text{(a.e.)}.
\]

This changes the game:
- boundary zeros no longer directly create \(\log|\cdot|\)-type singularities in the *modulus*, since \(\log|\mathcal J|=0\) a.e. on the boundary;
- the main quantity to control becomes the **phase drift** \(w\), not \(\log|\xi|\) itself.

`CPM.tex` informally describes \(\mathcal J\) as “a zeta-normalized ratio obtained by dividing a Hilbert–Schmidt determinant for an Euler tail by an outer factor and by \(\xi\)” so that the boundary modulus is \(1\) a.e.

**Canonical candidate (pure complex analysis).** Independently of any “Euler tail determinant” model, there is a universal way to manufacture such a \(\mathcal J\) from \(\xi\) itself: take the (half-plane) inner–outer factorization of \(\xi\) on \(\Omega\). If \(\xi\) is of bounded type on \(\Omega\) (as expected for finite-order entire functions restricted to a half-plane), one can write
\[
\xi(s)=\mathcal J(s)\cdot \mathcal O(s),
\]
where \(\mathcal J\) is inner (so \(|\mathcal J|=1\) a.e. on the boundary) and \(\mathcal O\) is outer. In that case, the zeros of \(\mathcal J\) in \(\Omega\) are exactly the zeros of \(\xi\) with \(\Re\rho>1/2\), and the natural “zero measure” of \(\mathcal J\) is precisely the \(\sigma\)-weighted measure \(\mu=\sum(\Re\rho-1/2)\,\delta_{(\Im\rho,\Re\rho-1/2)}\) that appears in (B′).

### 4.2. Minimal sufficient lemma in this architecture (local phase-certificate ⇒ wedge)

The “certificate” formulation in `CPM.tex` is:

> If there exist admissible test bumps \(\phi_I\) adapted to a Whitney schedule of intervals \(I\) such that for some \(\Upsilon<1/2\),
> \[
> \sup_I \int_{\mathbb R}\phi_I(t)\,(-w'(t))\,dt \le \pi\,\Upsilon,
> \]
> then after a unimodular rotation, \(|w(t)|\le \pi\Upsilon\) for a.e. \(t\) (a quantitative boundary wedge).

**Important normalization note.** As stated, “unit-mass bumps” \(\int \phi_I=1\) do *not* naturally produce a scale-decaying bound from a Carleson energy estimate; in the Carleson/CR–Green setup one typically uses a bump with \(\|\phi_I\|_2\sim |I|^{-1/2}\) (so that a \(|I|\)-energy bound cancels a \(|I|^{-1/2}\) boundary normalization factor).
So any attempt to implement this rigorously should fix the precise normalization of \(\phi_I\) and the exact inequality being tested.

### 4.3. The “one missing analytic input” in this architecture

Both in `CPM.tex` and in the standard CR–Green/Carleson toolbox, the quantitative certificate reduces to a uniform **Carleson box energy** bound for a harmonic function \(U\) related to \(\mathcal J\), typically

\[
U(t,\sigma) := \Re\log \mathcal J(1/2+\sigma+it),
\]

namely:

> **(J-Carleson)** There exists \(C_{\rm box}^{(\zeta)}<\infty\) such that for every boundary interval \(I\),
> \[
> \iint_{Q(I)} |\nabla U|^2\,\sigma\,dt\,d\sigma \le C_{\rm box}^{(\zeta)}\,|I|.
> \]

If one could further show that the tested boundary functional is bounded by a universal constant times \(\sqrt{C_{\rm box}^{(\zeta)}}\), then the entire wedge program becomes quantitative and auditable (the remaining steps are classical Herglotz/Schur transport plus a “pinch” argument).

**Quantitative target (just algebra).** In the CR–Green framework used elsewhere in this repo, the tested bound typically has the form
\[
\left|\int \phi_I(t)\,(-w'(t))\,dt\right|\ \le\ C_{\rm geom}\,\sqrt{C_{\rm box}^{(\zeta)}}
\]
for appropriately normalized bumps \(\phi_I\). Comparing with the certificate threshold \(\pi\Upsilon\) shows that one would need
\[
\Upsilon\ \le\ \frac{C_{\rm geom}}{\pi}\sqrt{C_{\rm box}^{(\zeta)}}\ <\ \frac12,
\]
equivalently
\[
C_{\rm box}^{(\zeta)}\ <\ \Big(\frac{\pi}{2C_{\rm geom}}\Big)^2.
\]
For the normalization \(C_{\rm geom}=1/2\) used in the Lean development, this is the concrete numeric target
\[
C_{\rm box}^{(\zeta)}\ <\ \pi^2 \approx 9.87.
\]
So, in this architecture, the “make it quantitative” bottleneck is not an astronomically small constant; it is the existence of a *uniform-in-height* Carleson box energy bound at all.

At present, `CPM.tex` leaves \(C_{\rm box}^{(\zeta)}\) schematic (written as \(K_0+K_\xi\), “unconditional tail + neutralized zeros”). Concretely, to make this route rigorous one must:
- define \(\mathcal J\) explicitly and verify it is holomorphic and nonvanishing on the Carleson boxes where \(U=\Re\log\mathcal J\) is invoked;
- prove (J-Carleson) with a *numerical* bound (not growing like \(\log |t_0|\));
- verify the exact boundary functional identity linking \(w'(t)\) to boundary normal derivatives of \(U\) (Hilbert transform / Cauchy–Riemann on the half-plane).

### 4.4. What this buys relative to §1–§2

This boundary-certificate route avoids the specific “\(\log|\xi|\) has unavoidable \(\ge 2/e\) local BMO floor” obstruction, because it works with a **different object** whose boundary modulus is already unimodular.
It does *not* automatically solve the deeper “uniform-in-height control” problem: proving a uniform Carleson energy bound for \(U=\Re\log\mathcal J\) is still a highly nontrivial analytic-number-theory statement.

### 4.5. Concrete analytic bridge: inner factors, zeros as a measure, and Poisson kernels

If \(\mathcal J\) is of bounded type on \(\Omega=\{\Re s>1/2\}\) and admits an inner–outer factorization, then the **inner** part is what carries zeros in \(\Omega\), while the boundary modulus constraint \(|\mathcal J(1/2+it)|=1\) a.e. forces \(\mathcal J\) to be (essentially) inner.

In the model case where \(\mathcal J\) is a Blaschke product in the half-plane with zeros
\[
a_n=\tfrac12+\sigma_n+i\gamma_n,\qquad \sigma_n>0,
\]
the boundary phase derivative has the explicit Poisson-kernel form (a.e.)
\[
\frac{d}{dt}\Arg\mathcal J\big(\tfrac12+it\big)
\;=\;\sum_n \frac{2\sigma_n}{(t-\gamma_n)^2+\sigma_n^2}
\quad\text{(plus an additional singular contribution if a singular inner factor is present).}
\]

Equivalently, defining the discrete “zero measure”
\[
\nu:=\sum_n \delta_{(\gamma_n,\sigma_n)},
\]
the boundary phase derivative is exactly a Poisson balayage of the **counting** measure \(\nu\):
\[
\frac{d}{dt}\Arg\mathcal J\big(\tfrac12+it\big)
\;=\;2\pi \int P(t-\gamma,\sigma)\,d\nu(\gamma,\sigma),
\qquad
P(x,\sigma)=\frac{1}{\pi}\frac{\sigma}{x^2+\sigma^2}.
\]

If one insists on using the \(\sigma\)-weighted measure
\[
\mu:=\sum_n \sigma_n\,\delta_{(\gamma_n,\sigma_n)},
\]
then the same identity can be rewritten as a balayage of \(\mu\) but with a *different kernel*:
\[
\frac{d}{dt}\Arg\mathcal J\big(\tfrac12+it\big)
\;=\;2\pi \int Q(t-\gamma,\sigma)\,d\mu(\gamma,\sigma),
\qquad
Q(x,\sigma):=\frac{1}{\pi}\frac{1}{x^2+\sigma^2}=\frac{1}{\sigma}\,P(x,\sigma).
\]
This matters: \(Q\) has an extra \(1/\sigma\) compared to the Poisson kernel, so a Carleson bound on the \(\sigma\)-weighted measure \(\mu\) does **not** automatically control the pointwise size of the integral unless one has additional information preventing too much mass near \(\sigma=0\).

**Practical implication.** If one tries to control \(w'(t)\) directly via Carleson packing, the “natural” measure is the counting measure \(\nu\), not the \(\sigma\)-weighted measure \(\mu\). But a Carleson condition for \(\nu\) is extremely strong: it essentially bounds the *number* of zeros in every Carleson box linearly in the base length, which is incompatible with the known average zero density \(\asymp \log T\) at height \(T\) unless the interval lengths are restricted in a height-dependent way. This is one reason `CPM.tex` phrases the missing input in terms of a **Dirichlet-energy Carleson bound** for \(U=\Re\log\mathcal J\) rather than a simple zero-counting Carleson condition.

This is the exact place where a Carleson packing statement for \(\mu\) (or a Carleson-energy statement for \(U=\Re\log\mathcal J\)) becomes the right quantitative hypothesis: it is what bounds tested integrals of \(w'(t)\) against bump functions.

**References** (for this bridge in equivalent forms): Garnett’s *Bounded Analytic Functions* (inner–outer factorization and boundary phase), and standard Hardy-space texts on half-plane Blaschke products and Poisson balayage.

---

## 5) A concrete “next lemma” package (CPM route, fully explicit)

The discussion in §4 can be distilled into a single, quantitative analytic target that is independent of the (false) formulation of (A′):

### 5.1. Objects and normalizations

Work in the shifted half-plane \(\Omega=\{\sigma>0\}\) with boundary parameter \(t\in\mathbb R\), corresponding to \(s=1/2+\sigma+it\).

Let \(\mathcal J\) be holomorphic on \(\Omega\) and of bounded type, with boundary unimodularity:
\[
|\mathcal J(it)|=1\quad\text{for a.e. }t\in\mathbb R.
\]
Define the harmonic potential
\[
U(t,\sigma):=\Re\log \mathcal J(\sigma+it).
\]
Then \(U(\cdot,0)=0\) a.e. on the boundary.

Let \(w(t):=\Arg \mathcal J(it)\) denote the boundary phase (a.e.). By Cauchy–Riemann on \(\Omega\),
\[
w'(t) = \partial_t w(t) = -\partial_\sigma U(t,0)\qquad\text{(a.e., in the distributional sense).}
\]

For an interval \(I_R=[t_0-L,t_0+L]\) with \(|I|=2L\), define the Carleson box
\[
Q(I):=\{(t,\sigma): t\in I_R,\ 0<\sigma\le 2|I|\}.
\]
(This matches the `carlesonBox` geometry used in the Lean module `CarlesonBound.lean`, up to harmless aperture constants.)

### 5.2. The tested functional bound (CR–Green + Cauchy–Schwarz)

Let \(\phi_I\) be a bump supported in \(I_R\) with \(L^2\) normalization
\[
\|\phi_I\|_2\le |I|^{-1/2}.
\]
Let \(V\) be the Poisson extension of \(\phi_I\) on \(\Omega\) (possibly with a smooth cutoff near the top of the box). Then the standard Green pairing identity on \(Q(I)\) gives
\[
\int_{I_R} \phi_I(t)\,(-\partial_\sigma U(t,0))\,dt
=\iint_{Q(I)} \nabla U\cdot\nabla V\ \sigma\,dt\,d\sigma.
\]
By Cauchy–Schwarz,
\[
\Big|\int_{I_R}\phi_I(t)\,(-w'(t))\,dt\Big|
\le \sqrt{E_U(I)}\;\sqrt{E_V(I)},
\]
where the box energies are
\[
E_U(I):=\iint_{Q(I)}|\nabla U|^2\,\sigma\,dt\,d\sigma,
\qquad
E_V(I):=\iint_{Q(I)}|\nabla V|^2\,\sigma\,dt\,d\sigma.
\]
For Poisson extensions one has a universal window-energy estimate \(E_V(I)\le \tfrac12\,\|\phi_I\|_2^2\le \tfrac{1}{2|I|}\). Consequently:
\[
\Big|\int_{I_R}\phi_I(t)\,(-w'(t))\,dt\Big|
\le \frac{1}{\sqrt{2}}\sqrt{\frac{E_U(I)}{|I|}}.
\tag{TestBound}
\]

### 5.3. Minimal sufficient analytic input (uniform Carleson-energy bound)

If there exists a constant \(C_{\rm box}\) such that
\[
E_U(I)\le C_{\rm box}\,|I|
\qquad\text{for all intervals }I,
\tag{J-Carleson}
\]
then (TestBound) simplifies to the scale-free bound
\[
\Big|\int_{I_R}\phi_I(t)\,(-w'(t))\,dt\Big|
\le \frac{1}{\sqrt{2}}\sqrt{C_{\rm box}}.
\]
In particular, a “certificate threshold” of the form \(\le \pi\Upsilon\) with \(\Upsilon<1/2\) will hold as soon as
\[
C_{\rm box}<2\pi^2\qquad\text{(under the \(\tfrac{1}{\sqrt2}\) constant above).}
\]

The exact numeric factor depends on the chosen aperture and on the sharp window-energy identity; the important point is that this is now a **single concrete inequality** (J-Carleson) about \(U=\Re\log \mathcal J\).

### 5.4. Reduction of (J-Carleson) to a zero packing statement (model case)

In the model case where \(\mathcal J\) is a Blaschke product on \(\Omega\) (no singular inner factor), \(U=\log|\mathcal J|\) is a sum of half-plane Green functions and its Dirichlet/Carleson energy is controlled by the \(\sigma\)-weighted zero measure
\[
\mu:=\sum_n \sigma_n\,\delta_{(\gamma_n,\sigma_n)}.
\]
More precisely, one expects an equivalence of the schematic form
\[
E_U(I)\ \asymp\ \mu(Q(I))
\]
(up to absolute multiplicative constants depending only on aperture), so (J-Carleson) becomes a Carleson packing condition for \(\mu\).
This is the point where analytic number theory enters: for the “canonical candidate” \(\mathcal J\) coming from the inner factor of \(\xi\), the zeros of \(\mathcal J\) are exactly the off-line zeros of \(\xi\) in \(\Omega\).

## Dependency checklist
- **Hardy (1914)**: infinitely many zeros of \(\zeta(1/2+it)\) on the critical line.
- **Basic holomorphic factorization**: local form \(F(t)=(t-t_*)^mG(t)\) near a zero.
- **Elementary BMO calculation**: \(\mathrm{meanOsc}(\log|t|;[-1,1])=2/e\).
- (Optional for §2.4) **Riemann–von Mangoldt + explicit \(S(T)\) bounds**: Trudgian (2012), `arXiv:1208.5846`, Theorem 1 (explicit bound on \(|S(T)|\)) and its Corollary 1 (explicit \(N(T)\) error term).

---

## 6) Formalizing the “\(\mathcal J\) = inner factor of \(\xi\)” candidate (what is standard vs what remains)

This section executes the next-step plan for Route 1: make precise what it would mean to take
\(\mathcal J\) as the inner factor of \(\xi\) on the half-plane \(\Re s>1/2\), and identify the exact analytic-number-theory input that is still missing to make the CPM route quantitative.

### 6.1. Reduce to the shifted half-plane

Write \(z:=s-\tfrac12\). Then \(\Re s>1/2\) becomes the right half-plane
\[
\Omega:=\{z\in\mathbb C:\Re z>0\}.
\]
Define \(F(z):=\xi(\tfrac12+z)\), which is holomorphic on \(\Omega\) (indeed entire).

### 6.2. “Bounded type” / Nevanlinna–Smirnov hypothesis for \(F\)

To speak about inner–outer factorization on \(\Omega\), one typically assumes \(F\) belongs to the Nevanlinna class \(N(\Omega)\) (bounded type), or better the Smirnov class \(N^+(\Omega)\). A standard sufficient condition is:
\[
\sup_{x>0}\ \int_{\mathbb R} \frac{\log^+|F(x+it)|}{1+t^2}\,dt < \infty.
\tag{BT}
\]

For \(F(z)=\xi(1/2+z)\), (BT) is expected to follow from standard growth bounds:
on vertical lines \(x=\Re z>0\), \(|\xi(1/2+x+it)|\) has at most polynomial growth in \(|t|\) (and in practice is tempered by the \(\Gamma\)-factor), so \(\log^+|F(x+it)|\lesssim \log(1+|t|)\), which is integrable against \((1+t^2)^{-1}\,dt\).

**Status:** this is classical analysis of \(\xi\) (Stirling + convexity bounds for \(\zeta\)); it is not yet written as a fully audited lemma in this repo.

### 6.3. Canonical factorization on \(\Omega\)

Assuming \(F\in N^+(\Omega)\), one has a canonical inner–outer factorization
\[
F(z)=\mathcal J(z)\cdot \mathcal O(z),
\]
where:
- \(\mathcal J\) is inner on \(\Omega\) (bounded analytic with \(|\mathcal J(it)|=1\) for a.e. \(t\)),
- \(\mathcal O\) is outer (analytic, zero-free on \(\Omega\), determined by boundary modulus).

Moreover, \(\mathcal J=\mathcal B\cdot \mathcal S\), a Blaschke product \(\mathcal B\) times a singular inner factor \(\mathcal S\).

**No singular inner factor (expected for \(F=\xi(1/2+\cdot)\)).** Since \(F\) extends holomorphically across the boundary line \(\Re z=0\) (it is entire), one expects \(\mathcal S\) to be trivial (a unimodular constant): singular inner factors encode boundary singularities, not merely isolated boundary zeros (which are a null set and do not affect a.e. boundary values).

**Status:** the factorization theorem is standard (Hardy-space/Nevanlinna theory on the half-plane); the “\(\mathcal S\) is trivial for entire \(F\)” step should be written carefully, but it is standard folklore in one-variable Hardy theory.

### 6.4. The Blaschke product \(\mathcal J\) and explicit factors

If \(\mathcal S\) is trivial, the inner factor \(\mathcal J\) is precisely the half-plane Blaschke product over the zeros of \(F\) in \(\Omega\), i.e. over the zeros \(\rho\) of \(\xi\) with \(\Re\rho>1/2\).

Writing such a zero as \(\rho=\tfrac12+\sigma+i\gamma\) with \(\sigma>0\), the corresponding zero in \(\Omega\) is \(a=\sigma+i\gamma\). The elementary Blaschke factor on \(\Omega\) is
\[
b_a(z):=\frac{z-a}{z+\overline{a}},
\]
since for \(z=it\) one has \(|it-a|=|it+\overline a|\). Then
\[
\mathcal J(z)=e^{i\theta}\prod_a b_a(z)
\]
with convergence governed by the half-plane Blaschke condition \(\sum_a \frac{\Re a}{1+|a|^2}<\infty\).

### 6.5. The natural “zero measure” and the CPM Carleson target

The \(\sigma\)-weighted discrete measure attached to the off-line zeros is
\[
\mu:=\sum_a (\Re a)\,\delta_{(\Im a,\Re a)} = \sum_{\Re\rho>1/2} (\Re\rho-\tfrac12)\,\delta_{(\Im\rho,\ \Re\rho-\tfrac12)}.
\]

As discussed in §4–§5, the CPM boundary-certificate route isolates a uniform Carleson-box energy bound as the key quantitative target:
\[
\iint_{Q(I)} |\nabla U|^2\,\sigma\,dt\,d\sigma \le C_{\rm box}\,|I|.
\tag{J-Carleson}
\]
In the pure Blaschke model, this kind of bound is equivalent (up to absolute constants depending only on aperture) to a Carleson packing bound for the weighted zero measure:
\[
\mu(Q(I))\le C\,|I|.
\tag{\(\mu\)-Carleson}
\]

### 6.6. What analytic-number-theory input is still missing?

The missing input is now completely explicit:

> Prove \((\mu\text{-Carleson})\) for the off-line zeros of \(\xi\) with a uniform constant \(C\) (independent of height).

This is materially stronger than what is provable from explicit \(N(T)\) bounds alone (which yield only \(\log\)-height dependent Carleson-type bounds, cf. §2.5). In other words: the remaining obstacle is to upgrade “height-dependent packing” to “uniform packing” for the \(\sigma\)-weighted measure \(\mu\).

---

## Appendix: Prompt/Response — \(\mu\)-Carleson

### Prompt (standalone)

```text
TASK: Prove or disprove a uniform Carleson packing bound for the σ-weighted off-line zero measure of the completed zeta function.

SETUP.
Let ξ(s) := (1/2) s(s-1) π^{-s/2} Γ(s/2) ζ(s) be the completed Riemann zeta function.
Its nontrivial zeros are the zeros ρ = β + iγ with 0<β<1 (counted with multiplicity).

Shift to the right half-plane:
  z := s - 1/2,  so  Re(s)>1/2  ⇔  Re(z)>0.
Define F(z) := ξ(1/2 + z). Then F is entire.

For each zero ρ of ξ with β>1/2, write it as
  ρ = 1/2 + σ + iγ   with  σ := β - 1/2 > 0, γ := Im(ρ).

Define the σ-weighted discrete measure on the upper half-plane (t,σ) coordinates:
  μ := ∑_{ρ: Re(ρ)>1/2} σ_ρ · δ_( (γ_ρ, σ_ρ) ).
(Count zeros with multiplicity.)

For an interval I_R := [t0 - L, t0 + L] (L>0), define |I| := 2L and the Carleson box (aperture fixed as 2):
  Q(I) := { (t,σ) : t ∈ I_R, 0 < σ ≤ 2|I| } = I_R × (0, 4L].

DEFINITION (μ-Carleson).
Say μ is a (uniform) Carleson measure if there exists an absolute constant C such that for every t0∈R and L>0,
  μ(Q(I)) ≤ C · |I|.

GOAL.
Either:
(A) Prove μ-Carleson for the actual ξ(s), with a fully explicit argument (and ideally an explicit C).
or:
(B) Disprove μ-Carleson (e.g. show it would imply an unproved strengthening of known zero-density results; or produce a conditional counterexample; or prove that known unconditional results cannot establish it).

REQUIRED ANALYSIS.
1) Make the “layer-cake” identity explicit:
   μ(Q(I)) = ∑_{ρ∈Q(I)} σ_ρ = ∫_0^{4L} N_I(u) du,
   where N_I(u) := #{ρ : γ_ρ∈I_R AND σ_ρ > u}.
   Note σ_ρ>u ⇔ Re(ρ) > 1/2 + u.

2) If you argue “(A) looks plausible,” you must supply the missing “sum over zeros” step cleanly:
   give a uniform bound on N_I(u) strong enough that ∫_0^{4L} N_I(u) du ≤ C|I|.

3) If you argue “(B),” quantify the obstruction precisely:
   - show what μ-Carleson would imply for local counts:
       for any η>0,  η · #{ρ: γ∈I_R, σ≥η} ≤ μ(Q(I)) ≤ C|I|
       hence #{ρ: γ∈I_R, σ≥η} ≤ (C/η)|I|.
   - in particular, for L≥1/8 the box includes all σ<1/2 so μ(Q(I)) is the full σ-sum of off-line zeros in the window;
     use this to deduce a strong restriction on the density of off-line zeros per unit height.
   - compare to what is currently known unconditionally (global N(T), global N(σ,T), any local-in-window results if available).

OPTIONAL (high value if you can do it):
Relate μ-Carleson to a Carleson-energy bound for the harmonic function U = Re log J where J is the inner factor of F on Re z>0.
In the pure Blaschke case (no singular inner factor), the expected equivalence is:
  μ-Carleson  ⇔  (Dirichlet/Carleson energy of U is Carleson on boxes),
up to absolute constants (depending only on aperture). Cite a standard reference (Garnett, Rosenblum–Rovnyak, etc.) and translate disk ↔ half-plane if needed.

DELIVERABLE.
A single writeup (no Lean) containing:
- exact definitions,
- a proof or a sharp “cannot be proved / implausible because it implies X” argument,
- citations with theorem numbers/sections,
- and the best unconditional substitute statement you can justify if μ-Carleson fails (e.g. a log-height dependent bound).
```

### Response (current best resolution)

#### Executive conclusion
- **\(\mu\)-Carleson is currently neither provable nor disprovable from known unconditional facts about \(\xi\)** (in the sense of a definitive theorem about the actual zeta zeros). It is a **genuinely new local packing hypothesis** about off-line zeros.
- What can be done (and is done above in this note) is:
  - derive the **best fully-auditable unconditional substitute**, which is **height-dependent** (grows like \(\log(|t_0|+L)\)), and
  - spell out exactly what \(\mu\)-Carleson would *imply* (uniform local density control for off-line zeros at every scale).

#### Setup (exact definitions)
Let
\[
\xi(s):=\tfrac12\,s(s-1)\,\pi^{-s/2}\Gamma(s/2)\zeta(s),
\]
and let its nontrivial zeros be \(\rho=\beta+i\gamma\) (multiplicity counted), with \(0<\beta<1\).

For \(\beta>1/2\), write
\[
\rho=\tfrac12+\sigma+i\gamma,\qquad \sigma=\beta-\tfrac12\in(0,\tfrac12).
\]

For \(I_R=[t_0-L,t_0+L]\) with \(L>0\), set \(|I|:=2L\) and
\[
Q(I):=I_R\times(0,4L].
\]

Define the \(\sigma\)-weighted discrete measure
\[
\mu:=\sum_{\Re\rho>1/2}\sigma_\rho\,\delta_{(\gamma_\rho,\sigma_\rho)}.
\]

**\(\mu\)-Carleson** means: \(\exists C\) such that for all \(t_0\in\mathbb R\), \(L>0\),
\[
\mu(Q(I))\le C\,|I|.
\]

#### 1) Correct “layer-cake” identity (with the \(\sigma\le 4L\) truncation)
By definition,
\[
\mu(Q(I))=\sum_{\substack{\Re\rho>1/2\\ \gamma_\rho\in I_R\\ 0<\sigma_\rho\le 4L}} \sigma_\rho.
\]
For each term, \(\sigma_\rho\,\mathbf 1_{\sigma_\rho\le 4L}=\int_0^{4L}\mathbf 1_{(u<\sigma_\rho\le 4L)}\,du\). Summing gives:
\[
\mu(Q(I))=\int_0^{4L} N_I(u)\,du,
\]
where
\[
N_I(u):=\#\{\rho:\ \gamma_\rho\in I_R,\ u<\sigma_\rho\le 4L\}.
\]
For **\(L\ge 1/8\)**, we have \(4L\ge 1/2\), so \(\sigma_\rho\le 4L\) is automatic, and then
\[
\mu(Q(I))=\int_0^{1/2}\#\{\rho:\gamma_\rho\in I_R,\ \sigma_\rho>u\}\,du.
\]

#### 2) What \(\mu\)-Carleson would imply (sharp, local consequences)
Assume \(\mu(Q(I))\le C|I|\).

- **Local count bound away from the line (for \(L\ge 1/8\))**: for any \(\eta\in(0,1/2)\) and any interval \(I_R\) with \(|I|\ge 1/4\),
  \[
  \eta\cdot \#\{\rho:\gamma_\rho\in I_R,\ \sigma_\rho\ge \eta\}
  \le \sum_{\gamma_\rho\in I_R}\sigma_\rho
  =\mu(Q(I))
  \le C|I|.
  \]
  Hence
  \[
  \#\{\rho:\gamma_\rho\in I_R,\ \Re\rho\ge 1/2+\eta\}\ \le\ \frac{C}{\eta}\,|I|.
  \tag{Local-density(η)}
  \]
  This is a **uniform-in-height, local-in-window** density control for off-line zeros.

- **Global density bound as a corollary**: covering \([0,T]\) by \(O(T)\) disjoint intervals of length \(1\) and applying \(\mu\)-Carleson to each yields
  \[
  \sum_{\substack{0<\gamma_\rho\le T\\ \Re\rho>1/2}}\sigma_\rho\ \ll\ T.
  \]
  Then for any \(\eta>0\),
  \[
  N(1/2+\eta,T)=\#\{\rho:0<\gamma_\rho\le T,\ \sigma_\rho\ge \eta\}
  \le \frac{1}{\eta}\sum_{0<\gamma_\rho\le T}\sigma_\rho
  \ll \frac{T}{\eta}.
  \tag{Global-density(η)}
  \]

**Bottom line**: \(\mu\)-Carleson is equivalent to very strong **uniform local packing control** of off-line zeros (not just global asymptotics).

#### 3) Why this is not currently obtainable from known unconditional results
Known unconditional tools fall into two buckets:

- **Explicit zero counting \(N(T)\)** (Riemann–von Mangoldt with explicit error): controls the total number of zeros in a window but **does not weight by \(\sigma\)** and does not isolate \(\Re\rho>1/2\). It yields \(\#\{\rho:\gamma\in I_R\}\sim |I|\log T\), hence only \(\mu(Q(I))\lesssim |I|\log T\) via the trivial \(\sigma\le 1/2\) bound.

- **Zero-density theorems \(N(\sigma,T)\)** (for fixed \(\sigma>1/2\)): they are primarily **global in \(T\)** and do not provide the **uniform local-in-window** bound (Local-density(η)) required for \(\mu\)-Carleson. In particular, they do not rule out strong local clustering of off-line zeros in short intervals.

So the status is:
- \(\mu\)-Carleson is **consistent with** what is known,
- but is **not implied by** existing unconditional zero-density technology, because it demands uniform local control at every scale.

#### 4) Best unconditional substitute we can actually prove today (explicit, auditable)
A simple unconditional bound uses only \(\sigma_\rho<1/2\):
\[
\mu(Q(I))\le \frac12\cdot \#\{\rho:\gamma_\rho\in I_R\}.
\]
Then insert an explicit \(N(T)\) estimate (Riemann–von Mangoldt with explicit error). One classical explicit bound is Rosser–Schoenfeld (1962):
\[
\left|N(T)-\left(\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+\frac78\right)\right|
\le 0.137\log T+0.443\log\log T+1.588\qquad(T\ge 2).
\]
From this (via a direct windowing/difference estimate), one gets an explicit height-dependent bound
\[
\mu(Q(I)) \le \Big(A\log U + B\log\log U + D\Big)\,|I|,\quad U:=\max(3,|t_0|+L),
\]
with explicit constants \(A,B,D\). A fully worked-out instance is given in §2.5 above as `(RS-Carleson(U))`.

#### 5) Optional bridge: \(\mu\)-Carleson ⇔ Carleson energy for \(U=\Re\log \mathcal J\)
If \(\mathcal J\) is taken as the inner factor of \(F(z)=\xi(1/2+z)\) on \(\Re z>0\), then in the “pure Blaschke” model (no singular inner factor) the weighted zero measure
\[
\mu=\sum \sigma\,\delta_{(\gamma,\sigma)}
\]
is the natural object controlling the Carleson-box Dirichlet energy of \(U=\Re\log\mathcal J\). This is why \(\mu\)-Carleson is the right “one-missing-input” target in the CPM boundary-certificate route.

#### Final status
- **(A) Prove \(\mu\)-Carleson**: not currently achievable from standard unconditional results in the literature (would require a new uniform local packing theorem for off-line zeros).
- **(B) Disprove \(\mu\)-Carleson**: also not currently possible, because we do not know the off-line zero configuration of \(\xi\).

So: \(\mu\)-Carleson is an explicit, sharply formulated open analytic input. The best unconditional substitute is an explicit log-height Carleson-type bound (as in §2.5).

---

## 7. Route 2: repairing the RG renormalized-tail route (make the statement true)

This section is about **surgically repairing the “renormalized tail is small” statement** so it is:
- **well-typed** for actual \(\xi\)-zeros (\(0<\Re\rho<1\)),
- **not vacuous** at large height,
- and **honest** about the required “sum over zeros” step (no “\(\sup_\rho\)” in place of \(\sum_\rho\)).

It is *not* a proof; it is the cleaned-up target and the minimal analytic input it really needs.

### 7.1. Two hard failures in the current formulation (why it must change)

- **Empty annuli for large \(L\)**: the definition in `riemann-recognition-geometry.tex` uses \(\sigma\in[0.75L,1.5L]\) etc. But for actual zeta zeros, \(\sigma\) is either \(\Re\rho\in(0,1)\) or \(d:=\Re\rho-\tfrac12\in(0,\tfrac12)\). Either way, \(\sigma\) is **bounded**, while Whitney interval lengths used elsewhere were taken **comparable to \(|\Im\rho|\)**, hence huge. That makes \(B(I,K)\) **literally empty** for most relevant \(I\).

- **Boundary-zero obstruction (\(\ge 2/e\) floor)**: any tail/BMO hypothesis applied directly to \(\log|\xi(\tfrac12+it)|\) (or a variant differing only on a null set) inherits the classical fact that \(\log|t|\) has a positive BMO lower bound (e.g. \(\approx 2/e\)) coming from logarithmic singularities at boundary zeros. To even *state* a “\(\le 0.20\)” type bound, you must **renormalize out the critical-line zeros locally** (or avoid them by construction).

- **The “annulus decay” bound as written is not a bound on the tail**: it controls
  \[
  \sum_{j>K}\sup_{\rho\in A_j}\int_I P(t-\gamma_\rho,\sigma_\rho)\,dt,
  \]
  which is unrelated to the required
  \[
  \sum_{j>K}\sum_{\rho\in A_j}\int_I P(t-\gamma_\rho,\sigma_\rho)\,dt.
  \]
  Any repaired route must supply (or assume) a **packing bound** that replaces the missing “\(\sum_{\rho\in A_j}\)” step.

### 7.2. Repair #1: choose the Whitney scale from the *off-line distance* \(d\), not the height \(|\gamma|\)

If \(\rho=\tfrac12+d+i\gamma\) with \(d>0\), the Blaschke/argument contribution across the symmetric interval \(I=[\gamma-L,\gamma+L]\) is
\[
\Delta_\rho(I)=2\arctan(L/d).
\]
So a constant phase signal threshold \(\Lrec\approx 2.2\) is achieved by choosing a **scale ratio** \(L/d\gtrsim\tan(\Lrec/2)\approx 2\), i.e.
\[
L \approx 2d.
\]
This fixes the “nonempty annuli” issue automatically, because \(d\le 1/2\) forces \(L\le 1\): the “vertical” coordinate is now on a scale where the strip bound does not trivialize the geometry.

In other words: the natural Whitney philosophy here is **Whitney on the half-plane \(\Re(s)-\tfrac12>0\)**, where the boundary interval length is comparable to the height \(d\).

### 7.3. Repair #2: renormalize out critical-line zeros locally (remove the log singularities)

To avoid the universal BMO floor caused by \(\sigma=0\) boundary zeros, the renormalization must subtract them.

One clean way is:
- define the local zero set \(B(I,K)\) to include **all** zeros \(\rho=\beta+i\gamma\) with \(|\gamma-t_0|\) in the chosen window, including \(\beta=\tfrac12\) (so \(d=0\)),
- subtract the corresponding local “log-distance” potentials \(\frac12\log((t-\gamma_\rho)^2+d_\rho^2)\) for \(d_\rho:=|\beta-\tfrac12|\).

This way, the “tail” is designed to be a **zero-free (or at least zero-removed) boundary datum** on \(I\), so a small oscillation hypothesis is no longer immediately falsified by point singularities.

### 7.4. Repair #3: replace the fake annulus bound with the real required packing input

After Repairs #1–#2, the only remaining obstacle in the RG tail step is:

> controlling the sum over zeros outside the local region, not just the supremum of a single zero.

Concretely, any Poisson-kernel based tail bound requires something of the schematic form
\[
\sum_{\rho\ \text{outside }B(I,K)} \int_I P(t-\gamma_\rho, d_\rho)\,dt \ \le\ C_{\rm tail},
\]
uniformly in the interval \(I\) (with \(L\) chosen as a function of \(d\)).

And that, in turn, is essentially equivalent to a **Carleson packing bound** for an appropriate zero measure:
- if you keep the \(d\)-weight, you get a \(\mu\)-type condition (as in Route 1),
- if you do not, you get a stronger “counting Carleson” condition for the counting measure \(\nu:=\sum \delta_{(\gamma_\rho,d_\rho)}\),
- if you include boundary zeros, you need an additional local control on zeros with \(d=0\) inside each \(I\).

So the “repaired Route 2” is honest about the bottleneck: it collapses back into a **packing/Carleson statement about zeros** (Route 1 in different clothing), unless one supplies a brand-new mechanism that controls these sums without a packing hypothesis.

### 7.5. What we can still prove unconditionally after these repairs

Without new input, you can at best recover **height-dependent** bounds (via \(N(T)\), cf. §2.5), which scale like
\[
C_{\rm tail}(t_0,L)\ \sim\ \log(\max(3,|t_0|+L)).
\]
This is mathematically correct but **does not close** the RG contradiction because the signal \(\Delta_\rho(I)\) is bounded by \(\pi\) while the noise bound grows (slowly) without bound.

### 7.6. Practical next step (if we implement Route 2 in Lean)

To reflect the repaired route in the formal pipeline, the minimal refactor is:
- **(a)** change the “interval selection” lemmas so that \(I.len\) is chosen **proportional to \(d=\Re\rho-\tfrac12\)** (not \(|\Im\rho|\));
- **(b)** redefine the “local zero set” used in tail renormalization so it cannot be empty for large \(|\Im\rho|\), and optionally includes \(\Re\rho=\tfrac12\) zeros in the subtraction;
- **(c)** replace the current “annulus decay” bound by an explicit **packing hypothesis** (or a target theorem) strong enough to justify the missing \(\sum_{\rho}\) step.

If you want, I can draft the precise repaired definitions (for \(B(I,K)\), the repaired \(f_{\mathrm{tail}}^I\), and the exact packing lemma needed) in the notation already used by the Lean codebase, so the refactor is mechanical.

### 7.7. Lean implementation status (Route 2 repair)

**Repair #1 (interval scale from off-line distance)** has been implemented in `Axioms.lean`:

- **`blaschke_dominates_total_centered`**: a new theorem that, given an off-line zero \(\rho\) with \(d:=\Re\rho-\tfrac12>0\), constructs the Whitney interval \(I_0\) with center \(\gamma=\Im\rho\) and half-length \(L=2d\). For this interval, the Blaschke phase is exactly \(2\arctan 2>2.2=L_{\rm rec}\), which dominates the tail bound.

- **`zero_free_with_interval`**: updated to call `blaschke_dominates_total_centered` directly, so the contradiction now works for *any* off-line zero (no "height > 14" or "width comparable to height" side conditions).

**What remains open:**
- The contradiction still relies on `RGAssumptions.weierstrass_tail_bound_axiom_statement`, which asserts that the phase tail is at most \(U_{\rm tail}(M)\). This assumption is *schematically* the same as before, but now the interval scale is tied to \(d\), making the statement geometrically coherent.

- To *prove* that assumption unconditionally, one still needs a **packing/Carleson bound** for the distant zeros (Repair #3). That step is exactly the \(\mu\)-Carleson target from Route 1 — no free lunch.

**Takeaway:** the Lean RG chain is now internally consistent at the geometric level (no vacuously true hypotheses about non-existent interval/zero configurations), but the outstanding analytic input is unchanged: \(\mu\)-Carleson (or an equivalent packing statement) for the \(\sigma\)-weighted off-line zero measure.

---

## 8) Route 3 (major rebuild): Weil explicit formula / Li positivity (no Carleson/BMO)

This route **abandons the boundary-Whitney/Carleson infrastructure entirely**.  Instead of trying to control a boundary phase locally (a wedge certificate) via a uniform Carleson-box energy bound, it reframes RH as an **explicit-formula positivity** statement and targets that positivity directly.

### 8.1. What changes (and why it’s genuinely different)

- **Old bottleneck (local)**: prove a *uniform local* packing/energy statement (e.g. \(\mu\)-Carleson or (J-Carleson)) controlling off-line zeros in every Carleson box at every height and scale.
- **New bottleneck (global)**: prove a *global positivity* statement attached to the Guinand–Weil explicit formula:
  - positivity of a quadratic form \(f\mapsto W^{(1)}(f*\widetilde{\overline f})\) on a space of test functions (Weil), or
  - positivity of a countable sequence \((\lambda_n)\) (Li).

The rebuild is conceptual: the “certificate” is no longer a local wedge extracted from harmonic-analysis norms; it is an explicit-formula quadratic form.

### 8.2. Lagarias’ normalization: Mellin transform, convolution, involution, and “nice” tests

We fix the Mellin-transform conventions and the explicit-formula functionals exactly as in Lagarias (2007, §3).

#### 8.2.1. Mellin transform and multiplicative convolution

For \(f:(0,\infty)\to\mathbb C\), define the Mellin transform
\[
M[f](s)\ :=\ \int_0^\infty f(x)\,x^{s}\,\frac{dx}{x}\qquad(s\in\mathbb C).
\]

Define multiplicative convolution by
\[
(f*g)(x)\ :=\ \int_0^\infty f\!\left(\frac{x}{y}\right)\,g(y)\,\frac{dy}{y}.
\]
Then
\[
M[f*g](s)=M[f](s)\,M[g](s).
\]

#### 8.2.2. Involution

Define the involution
\[
\widetilde f(x)\ :=\ \frac{1}{x}\,f\!\left(\frac{1}{x}\right).
\]
Then
\[
M[\widetilde f](s)=M[f](1-s).
\]

#### 8.2.3. “Nice” test functions (Lagarias’ class)

In Lagarias’ §3, the explicit formula is stated for test functions \(f:(0,\infty)\to\mathbb C\) that are:
- piecewise \(C^2\),
- compactly supported,
- and satisfy the averaging convention at jump discontinuities:
\[
f(x)\ :=\ \frac12\Big(\lim_{t\to x+}f(t)+\lim_{t\to x-}f(t)\Big).
\]

This class is stable under the map \(f\mapsto f*\widetilde{\overline f}\).

### 8.3. The explicit-formula functionals \(W_{\mathrm{spec}},W_{\mathrm{arith}},W^{(j)}\)

Let \(\xi(s)\) denote the completed zeta function in **Lagarias’ normalization**:
\[
\xi(s)\ :=\ \frac12\,s(s-1)\,\pi^{-s/2}\Gamma\!\Big(\frac{s}{2}\Big)\,\zeta(s).
\]
It is entire and satisfies \(\xi(s)=\xi(1-s)\); its nontrivial zeros coincide with those of \(\zeta(s)\).
Let \(\{\rho\}\) be the multiset of nontrivial zeros of \(\xi\), counted with multiplicity.

Define the “spectral” components:
\[
W^{(2)}(f)\ :=\ M[f](1),\qquad
W^{(0)}(f)\ :=\ M[f](0),
\]
\[
W^{(1)}(f)\ :=\ \sum_{\rho\ \text{zero of }\xi} M[f](\rho),
\]
where the sum is interpreted in the standard symmetric way (pairing \(\rho\) with \(1-\rho\), or as a limit over \(|\Im\rho|\le T\) as \(T\to\infty\)); for the “nice” class above, Lagarias proves convergence in §3.

Then define the “spectral side”
\[
W_{\mathrm{spec}}(f)\ :=\ W^{(2)}(f)\ -\ W^{(1)}(f)\ +\ W^{(0)}(f).
\]

Define the “arithmetic” components. For a prime \(p\),
\[
W_p(f)\ :=\ (\log p)\sum_{n=1}^{\infty}\big(f(p^n)+\widetilde f(p^n)\big).
\]
At the archimedean place,
\[
W_\infty(f)\ :=\ (\gamma+\log\pi)\,f(1)\ +\ \int_{1}^{\infty}\frac{f(x)+\widetilde f(x)-\frac{2}{x^2}f(1)}{x^2-1}\,x\,dx,
\]
where \(\gamma\) is Euler’s constant.

Finally set
\[
W_{\mathrm{arith}}(f)\ :=\ W_\infty(f)\ +\ \sum_{p\ \text{prime}} W_p(f).
\]

### 8.4. Lagarias Theorem 3.1: the explicit formula (Mellin form)

> **Theorem 8.1 (Lagarias 2007, Thm. 3.1).** For any “nice” test function \(f:(0,\infty)\to\mathbb C\),
> \[
> W_{\mathrm{spec}}(f)\ =\ W_{\mathrm{arith}}(f).
> \]

This is the Guinand–Weil explicit formula in Lagarias’ Mellin-transform normalization.

### 8.5. Lagarias Theorem 3.2: Weil positivity (RH as positivity of a quadratic form)

> **Theorem 8.2 (Lagarias 2007, Thm. 3.2; Weil positivity).** The Riemann Hypothesis is equivalent to
> \[
> W^{(1)}(f*\widetilde{\overline f})\ \ge\ 0
> \qquad\text{for all “nice” test functions }f.
> \]

**Equivalent inequality on the arithmetic side.** Combining Theorem 8.1 with
\(
W^{(1)}(g)=W^{(2)}(g)+W^{(0)}(g)-W_{\mathrm{arith}}(g)
\)
gives:
\[
W^{(1)}(f*\widetilde{\overline f})\ge 0
\quad\Longleftrightarrow\quad
W_{\mathrm{arith}}(f*\widetilde{\overline f})\ \le\ W^{(2)}(f*\widetilde{\overline f})+W^{(0)}(f*\widetilde{\overline f}).
\]
Since \(M[f*\widetilde{\overline f}](s)=M[f](s)\,\overline{M[f](1-\overline s)}\), one has
\[
W^{(2)}(f*\widetilde{\overline f})+W^{(0)}(f*\widetilde{\overline f})
= 2\,\Re\!\big(M[f](1)\,\overline{M[f](0)}\big),
\]
so Weil positivity can be read as a **pure inequality** between the prime-power side \(W_{\mathrm{arith}}\) and the boundary Mellin data \(M[f](0),M[f](1)\).

### 8.6. Li coefficients (countable positivity criterion)

Define Li’s coefficients (Lagarias 2007, §6.3):
\[
\lambda_n\ :=\ \frac{1}{(n-1)!}\left.\frac{d^n}{ds^n}\Big(s^{n-1}\log\xi(s)\Big)\right|_{s=1},
\qquad n\ge 1.
\]

> **Theorem 8.3 (Li 1997; Lagarias 2007, Thm. 6.5).** RH is equivalent to
> \[
> \lambda_n\ \ge\ 0\qquad\text{for all }n\ge 1.
> \]

#### 8.6.1. Sum over zeros formula (with convergence convention)

There is a standard “sum over zeros” representation (Li; see also Bombieri–Lagarias):
\[
\lambda_n\ =\ \sum_{\rho}\left(1-\Big(1-\frac{1}{\rho}\Big)^{\!n}\right),
\]
where the sum is over all nontrivial zeros \(\rho\) of \(\xi\), counted with multiplicity, and is interpreted as a symmetric limit over \(|\Im\rho|\le T\) (or equivalently by pairing \(\rho\) with \(1-\rho\)) to ensure convergence.

Under RH, \(\rho=\tfrac12+i\gamma\) implies \(\left|\frac{\rho-1}{\rho}\right|=1\), hence \(\left(1-\frac{1}{\rho}\right)^n\) lies on the unit circle and
\(\Re\!\left(1-(1-1/\rho)^n\right)=1-\cos(n\theta_\rho)\ge 0\),
making the forward implication \(\mathrm{RH}\Rightarrow(\lambda_n\ge 0)\) transparent.

#### 8.6.2. Li as a special case of Weil positivity

Lagarias notes (citing Bombieri–Lagarias) that Li’s coefficients can be realized as Weil functionals:
\[
\lambda_n\ =\ W^{(1)}\!\big(\phi_n*\widetilde{\overline{\phi_n}}\big)
\]
for an explicit sequence \((\phi_n)\) of test functions.

**Caveat (important):** this \((\phi_n)\) falls outside the compact-support class used to state Theorem 8.1 in Lagarias’ §3, but the explicit formula can be extended/justified for these specific \(\phi_n\) (in a slightly modified form) and the identity still holds (Lagarias cites Bombieri–Lagarias for this).

### 8.7. Conrey–Li warning: de Branges shift-positivity is *too strong* (and false)

Conrey–Li (arXiv:math/9812166) analyze positivity conditions arising in de Branges’ Hilbert-space program, e.g. shift-positivity requirements of the schematic form
\[
\Re\langle F(z),F(z+i)\rangle_{\mathcal H(E)}\ge 0\quad\text{for all }F,
\qquad E(z)=\xi(1-iz),
\]
and related kernel-shift positivity conditions implying pointwise half-plane inequalities like \(\Re\{W(z)/W(z+i)\}\ge 0\) for certain \(W\) built from \(\xi\).

They give explicit counterexamples showing these **pointwise/shift** positivity conditions fail for \(\zeta\) (and \(L(s,\chi_4)\)).  So a “positivity rebuild” must target **Weil/Li averaged positivity**, not pointwise de Branges shift-positivity.

### 8.8. What would close the proof (minimal analytic input + plausible intermediates)

At this point the proof skeleton is completely explicit:

- **(Weil gate)** Prove Theorem 8.2’s inequality \(W^{(1)}(f*\widetilde{\overline f})\ge 0\) for all “nice” \(f\). Then RH follows.
- **(Li gate)** Prove \(\lambda_n\ge 0\) for all \(n\ge 1\). Then RH follows.

These are equivalent (both \(\Leftrightarrow\) RH), but they replace the prior **local** \(\mu\)-Carleson bottleneck by a single **global explicit-formula positivity** bottleneck.

Two concrete intermediate targets (still nontrivial, and plausibly “attackable” subproblems) are:

1. **Dense-subclass reduction for Weil positivity.** Show \(f\mapsto W^{(1)}(f*\widetilde{\overline f})\) is continuous in a topology under which smooth compactly supported functions are dense, so it suffices to check Weil positivity on a convenient dense subclass (e.g. \(C_c^\infty\) supported in \([e^{-A},e^{A}]\) with \(A\in\mathbb N\)). This reduces the “for all \(f\)” quantifier to a manageable basis, without changing the bottleneck’s nature.

2. **Explicit prime-power formula for \(\lambda_n\) with a uniform remainder bound.** Starting from Li’s explicit formulas for \(L\)-functions (or from Bombieri–Lagarias), derive a fully explicit prime-power expression for \(\lambda_n\) and prove a lower bound of the form
\[
\lambda_n \ \ge\ \frac{n}{2}\log n + c\,n - C\,n^\theta
\]
with some \(\theta<1\) and explicit constants \(c,C\). This would imply \(\lambda_n>0\) for all sufficiently large \(n\), reducing RH to verifying finitely many initial \(\lambda_n\) numerically/auditably. (For \(\zeta\), this remains out of reach unconditionally with current technology.)

---

### References (for Route 3)
- J. C. Lagarias, *The Riemann Hypothesis: Arithmetic and Geometry* (survey article, May 4, 2007): §3 Theorems 3.1–3.2; §6.3 Theorem 6.5.
- X.-J. Li, “The positivity of a sequence of numbers and the Riemann hypothesis,” *J. Number Theory* **65** (1997), 325–333.
- E. Bombieri and J. C. Lagarias, “Complements to Li’s criterion for the Riemann hypothesis,” *J. Number Theory* **77** (1999), 274–287.
- A. Weil, “Sur les ‘formules explicites’ de la théorie des nombres premiers,” *Comm. Sém. Math. Univ. Lund* (1952), 252–265.
- J. B. Conrey and X.-J. Li, “A note on some positivity conditions related to zeta- and \(L\)-functions,” preprint (1998), `arXiv:math/9812166`.
