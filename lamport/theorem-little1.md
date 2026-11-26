# Lamport Proof — Theorem 1 (Modified Little's Theorem for LIFO Systems)

*Provenance: Follows Appendix A of `arXiv:1008.4895v2` (L1019–1080), adapted to discrete slotted time $t \in \mathbb{N}$.*

**Theorem 1.** Let $\mathcal{B}$ be a finite set of single-occupancy LIFO buffer locations. Suppose with probability 1 that $\liminf_{t\to\infty} N(t)/t \ge \lambda_{\min} > 0$ and $\lim_{t\to\infty} D(t) = \infty$. Then with probability 1, $\limsup_{t\to\infty} \frac{1}{D(t)} \sum_{i=1}^{D(t)} W_i \le |\mathcal{B}| / \lambda_{\min}$.

1. **Restrict to an almost-sure sample path**
   - 1.1. **Fix a good sample path $\omega$**: Fix a sample path $\omega$ on which both $\liminf_{t\to\infty} N(t)/t \ge \lambda_{\min}$ and $D(t) \to \infty$ hold. The intersection of these two probability-1 events has probability 1.
     - *Uses:* Theorem 1 hypotheses
     - *Lean:* `Proofs.Little.theorem1_pathwise`

2. **Total delay upper bound ($\sum_{i=1}^{D(t)} W_i \le |\mathcal{B}| \cdot t$)**
   - 2.1. **Disjoint occupancy intervals per slot**: For each buffer slot $b \in \mathcal{B}$, single occupancy ensures any two distinct jobs assigned to $b$ have disjoint residency intervals $[a_k, d_k)$.
     - *Uses:* `BufferSystem.disjoint_slots`
     - *Lean:* `Proofs.Little.slot_delay_le`
   - 2.2. **Per-slot departing delay $\le t$**: Every job departing by time $t$ ($d_k \le t$) satisfies $[a_k, d_k) \subseteq \{0, \dots, t-1\}$, so $\sum_{k:\,\mathrm{slot}(k)=b,\, d_k \le t} W_k \le t$ (discrete analogue of Eq. 23 & Fig. 14).
     - *Uses:* `⟨1⟩2.⟨2⟩1`
     - *Lean:* `Proofs.Little.slot_delay_le`
   - 2.3. **Sum over all $b \in \mathcal{B}$**: Summing over all $b \in \mathcal{B}$ gives $\sum_{k:\, d_k \le t} W_k \le |\mathcal{B}| \cdot t$ for every $t \in \mathbb{N}$ directly, avoiding Appendix A's split into $\tilde{\mathcal{B}}$ and finite remainder $\mathcal{J}$.
     - *Uses:* `⟨1⟩2.⟨2⟩2`
     - *Lean:* `Proofs.Little.totalDelay_le`

3. **Departure lower bound ($D(t) \ge N(t) - |\mathcal{B}|$)**
   - 3.1. **Undeparted arrivals occupy distinct slots at time $t$**: Every job arriving before $t$ ($a_k < t$) that has not departed by $t$ ($d_k > t$) occupies its assigned slot $\mathrm{slot}(k) \in \mathcal{B}$ at slot $t$.
     - *Uses:* `BufferSystem.disjoint_slots`
     - *Lean:* `Proofs.Little.arrivals_le_departures_add_card`
   - 3.2. **At most $|\mathcal{B}|$ jobs remain in buffer**: Injectivity of $\mathrm{slot}$ on undeparted jobs yields $|\{k : a_k < t < d_k\}| \le |\mathcal{B}|$, hence $N(t) \le D(t) + |\mathcal{B}|$ and $D(t) \ge N(t) - |\mathcal{B}|$.
     - *Uses:* `⟨1⟩3.⟨2⟩1`
     - *Lean:* `Proofs.Little.arrivals_le_departures_add_card`

4. **Asymptotic $\limsup$ conclusion**
   - 4.1. **Eventual ratio bound for any $\varepsilon \in (0, \lambda_{\min})$**: Since $\liminf N(t)/t \ge \lambda_{\min}$ and $|\mathcal{B}|/t \to 0$, eventually $D(t)/t \ge \lambda_{\min} - \varepsilon > 0$. Combining `⟨1⟩2.⟨2⟩3` and `⟨1⟩3.⟨2⟩2` yields $\mathrm{avgDelay}(t) \le |\mathcal{B}| t / D(t) \le |\mathcal{B}| / (\lambda_{\min} - \varepsilon)$.
     - *Uses:* `⟨1⟩1.⟨2⟩1`, `⟨1⟩2.⟨2⟩3`, `⟨1⟩3.⟨2⟩2`
     - *Lean:* `Proofs.Little.theorem1`
   - 4.2. **Send $\varepsilon \to 0^+$ (Q.E.D.)**: Taking $\limsup_{t\to\infty}$ and letting $\varepsilon \to 0^+$ yields $\limsup_{t\to\infty} \mathrm{avgDelay}(t) \le |\mathcal{B}| / \lambda_{\min}$ almost surely. $\blacksquare$
     - *Uses:* `⟨1⟩4.⟨2⟩1`
     - *Lean:* `Assembly.theorem_little1`
