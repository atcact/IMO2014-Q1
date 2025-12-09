# IMO 2014 Q1

Let $a_0 < a_1 < a_2 < \dots$ be an infinite sequence of positive integers. Prove that there exists a unique integer $n\geq 1$ such that
$a_n < \frac{a_0+a_1+a_2+\cdots+a_n}{n} \leq a_{n+1}.$

Solution:
 Define sequence $(b_n)$, where $b_n=(a_n-a_{n-1})+\dots+(a_n-a_1)$. 
 Then $b_1=0$ and $(b_n)$ is a strictly increasing sequence.

Note that: $a_n < \frac{a_0+a_1+a_2+\cdots+a_n}{n} \leq a_{n+1} \Leftrightarrow b_n<a_0\leq b_{n+1}$


$(b_n)$ is a strictly increasing sequence of nonnegative integers and $b_1=0$, hence unbounded, so there exists $N>1$ such that $b_N \geq a_0$. Choose the smallest such $N$, which then gives $b_{N-1} < a_0$. So $N-1$ satisfies $b_{N-1} < a_0 \leq b_N$.

Assume there is another $N'$ satisfying $b_{N'} < a_0 \leq b_{N'+1}$:

1. $N' > N-1$: $b_{N'} \geq b_{N} \geq a_0$, contradiction.
2. $N' < N-1$: $b_{N'+1} \leq b_{N-1} < a_0$, contradiction.

Therefore, $N' = N-1$. There exists an unique $n$ such that $b_n<a_0\leq b_{n+1}$. Equivalently, there exists an unique $n$ such that $a_n < \frac{a_0+a_1+a_2+\cdots+a_n}{n} \leq a_{n+1} $

