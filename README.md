# Formalization of IMO 2014 - Q1

Let $a_0 < a_1 < a_2 < \dots$ be an infinite sequence of positive integers. Prove that there exists a unique integer $n\geq 1$ such that
$a_n < \frac{a_0+a_1+a_2+\cdots+a_n}{n} \leq a_{n+1}.$

*Solution:*

 Define sequence $(b_n)$, where $b_n=(a_n-a_{n-1})+\dots+(a_n-a_1)$. 
 Then $b_1=0$ and $(b_n)$ is a strictly increasing sequence.

Note that: $a_n < \frac{a_0+a_1+a_2+\cdots+a_n}{n} \leq a_{n+1} \Leftrightarrow b_n<a_0\leq b_{n+1}$


$(b_n)$ is a strictly increasing sequence of nonnegative integers and $b_1=0$, hence unbounded, so there exists $N>1$ such that $b_N \geq a_0$. Choose the smallest such $N$, which then gives $b_{N-1} < a_0$. So $N-1$ satisfies $b_{N-1} < a_0 \leq b_N$.

Assume there is another $N'$ satisfying $b_{N'} < a_0 \leq b_{N'+1}$:

1. $N' > N-1$: $b_{N'} \geq b_{N} \geq a_0$, contradiction.
2. $N' < N-1$: $b_{N'+1} \leq b_{N-1} < a_0$, contradiction.

Therefore, $N' = N-1$. There exists an unique $n$ such that $b_n<a_0\leq b_{n+1}$. Equivalently, there exists an unique $n$ such that $a_n < \frac{a_0+a_1+a_2+\cdots+a_n}{n} \leq a_{n+1} $. $\quad \square$

## Implementation in Lean
We follow the folling steps based on the solution above:
### Step 0: Definitions
First define the sequence $(a_n)$ as a function $\mathbb{N} \to \mathbb{N}$, mapping each index to a natural number, with two additional conditions: (1) stricly increasing (`StrictMono`), (2) All elements in the sequence are positive integers.

Next define the sequence $(b_n)$ as in the solution above, with an index shift by $1$ so that the sequence starts with index $0$, e.g.

$b_0 = 0, \quad b_1 = a_2-a_1, \quad b_2 = (a_3-a_2)+(a_3-a_1) \quad \dots$

### Step 1: Show that $(b_n)$ is a strictly increasing sequence.
Show by calculation that if $n < m$, then $b_n < b_m$.

### Step 2: Show the equivalence of inequalities between $(a_n)$ and $(b_n)$.
Show by calculation: 

$$a_n < \frac{a_0+a_1+a_2+\cdots+a_n}{n} \leq a_{n+1} \Leftrightarrow b_n<a_0\leq b_{n+1}.$$

### Step 3: Show the existence and uniqueness of $n$ that satisfies $b_n<a_0\leq b_{n+1}$.
- There exists $N$ such that $b_N ≥ a_0$.
- Find the smallest such $N$.
- Show that $n = N-1$ satisies $b_n<a_0\leq b_{n+1}$.
- Show the uniqueness of $n$ by contradiction: if there exists $m$ satisfying the inequality and $m \neq n$, then $m < n$ or $m > n$, either of which leads to contradiction. 

### Step 4: State and conclude the problem
```
theorem imo_problem :
∃! n, (a n : ℝ) < (∑ k ∈ Finset.range (n+1), a k) / n ∧
    (∑ k ∈ Finset.range (n+1), a k) / n ≤ (a (n+1) : ℝ)
```