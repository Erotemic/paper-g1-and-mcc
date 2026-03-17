We want to formalize this proof in lean4.

References:

    https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf
     

    https://www.ma.imperial.ac.uk/~buzzard/docs/lean/sandwich.html
    https://news.ycombinator.com/item?id=22799723
    https://stackoverflow.com/questions/75398131/prove-p-%E2%86%92-%C2%AC-q-%E2%86%92-%C2%AC-p-%E2%88%A7-q-in-lean4
    https://ahelwer.ca/post/2020-04-05-lean-assignment/
    https://leanprover-community.github.io/lean-web-editor/#code=import%20tactic%0A%0Adef%20sum_of_first_n_nat%20%3A%20%E2%84%95%20%E2%86%92%20%E2%84%95%0A%7C%200%20%3A%3D%200%0A%7C%20%28nat.succ%20n%29%20%3A%3D%20%28nat.succ%20n%29%20%2B%20sum_of_first_n_nat%20n%0A%0A%23eval%20sum_of_first_n_nat%204%0A%0Atheorem%20closed_eq_sum_of_first_n_nat%20%28n%20%3A%20%E2%84%95%29%20%3A%0A%20%20%20%202%20*%20%28sum_of_first_n_nat%20n%29%20%3D%20n%20*%20%28nat.succ%20n%29%20%3A%3D%0Abegin%0Ainduction%20n%20with%20d%20hd%2C%0A%20%20rw%20sum_of_first_n_nat%2C%0A%20%20rw%20nat.mul_zero%2C%0A%20%20rw%20nat.zero_mul%2C%0Arw%20sum_of_first_n_nat%2C%0Arw%20nat.left_distrib%2C%0Arw%20hd%2C%0A--rewrites%20nat.succ%20n%20to%20n%20%2B%201%3A%0Arw%20nat.succ_eq_add_one%2C%0A--rewrites%20nat.succ%20%28n%20%2B%20m%29%20to%20n%20%2B%20nat.succ%20m%20%28from%20defn%20of%20addition%29%0A--note%20rw%20usually%20rewrites%20from%20left%20to%20right%20over%20an%20equality%3B%20%E2%86%90%20%28%5Cl%29%20does%20right%20to%20left%0Arw%20%E2%86%90%20nat.add_succ%2C%0A--rewrites%20nat.succ%201%20to%202%0Arw%20%28show%20nat.succ%201%20%3D%202%2C%20by%20refl%29%2C%0A--multiplies%20out%20d%20%2B%201%0Arw%20left_distrib%20%28d%20%2B%201%29%20d%202%2C%0A--moving%20things%20around%20with%20commutativity%0Arw%20mul_comm%202%20%28d%20%2B%201%29%2C%0Arw%20mul_comm%20d%20%28d%20%2B%201%29%2C%0Arw%20add_comm%2C%0Aend%0A%0Atheorem%20closed_eq_sum_of_first_n_nat_with_ring%20%28n%20%3A%20%E2%84%95%29%20%3A%0A%20%20%20%202%20*%20%28sum_of_first_n_nat%20n%29%20%3D%20n%20*%20%28nat.succ%20n%29%20%3A%3D%0Abegin%0Ainduction%20n%20with%20d%20hd%2C%0A%20%20rw%20sum_of_first_n_nat%2C%0A%20%20ring%2C%0Arw%20sum_of_first_n_nat%2C%0Arw%20nat.left_distrib%2C%0Arw%20hd%2C%0Aring%2C%0Aend


https://en.wikipedia.org/wiki/Limit_of_a_function 


The definition of a limit:

    lim_{x -> p} f(x) = L

is true if: 

    (\forall x in \Real)  % this can be relatex to a subset of the domain around the limit
    (\forall \epsilon > 0) 
    (\exists \delta > 0)
    (0 < abs(x - p) < \delta  ==>  abs(f(x) - L) < \epsilon)


When p is infinite, we rewrite:


    lim_{x -> \inf} f(x) = L

    (\forall x in \Real)    % this can be relatex to a subset of the domain unbounded on the right
    (\forall \epsilon > 0) 
    (\exists c > 0)

    (x > c   ==>   abs(f(x) - L) < \epsilon)


For our case we need to show that given:

    lim_{x -> inf} 1 / x = 0


    x > c  ==>   abs(f(x) - 0) < \epsilon

    Recall  A ==> B    \equiv   not A or B

    So

    x <= c  or  abs(f(x)) < \epsilon

    for all epsilon there exists a c

    Let c = 1 / epsilon

    So we have for all x > 0 

          x <= 1 / eps    or    abs(1 / x) < eps


    The left side: x <= 1 / eps, rewrite:

         eps * x <= 1

         eps <= 1 / x

         1 / x >= eps

    On the right side: abs(1 / x) < eps, because x is positive, rewrite:

         1 / x < eps

    So now we have:

          1 / x >= eps   or   1 / x < eps

    Which is a tautology... but do we need to prove that formally?

```psuedo-lean4


See filter.tendsto

https://leanprover-community.github.io/theories/topology.html
https://leanprover-community.github.io/mathlib_docs/order/filter/basic.html#limits

def limit_to_inf: (f : ℝ+ → ℝ, L : ℝ):
    # If satisfied then lim_{x -> inf} f(x) = L
    ∀ ε > 0, ∃ c > 0

    (x > c   ==>   |f(x) - L| < ε
    



theorem one_over_inf_is_zero : ∀ ε > 0, ∃ c > 0, 


```


In SymPy we can show:

```python
from sympy import symbols, simplify
from sympy.series import limit, Or
x = symbols("x", negative=False, real=True)
f = 1 / x
limit(f, x, float('inf'))



c, eps = symbols("c, ε", negative=False, real=True)

# Need to show this is a tautology
goal = (x <= c) | (abs(1 / x) < eps)


# Define c in terms of epsilon

c_assign = 1 / eps
subgoal = goal.subs({c: c_assign})


simplify((1 / x > eps) | (1 / x < eps))
simplify((1 / x >= eps) | (1 / x < eps))

```    



%Here \code{MCC} and \code{FM} are the direct Lean definitions corresponding to
%the formulas in this paper. The full proof is 654 lines. It is available in
%these forms:

%https://github.com/Erotemic/paper-g1-and-mcc/blob/main/mcc-proof/MCC_atTop_eq_FM/WuAristotle.lean
%\begin{itemize}
%\item GitHub permalink: \\
%\href{https://github.com/Erotemic/paper-g1-and-mcc/blob/89dc05e80432f727cc41f07ecfeda5c87e69945d/mcc-proof/MCC_atTop_eq_FM/WuAristotle.lean}{%
%    \texttt{https://github.com/Erotemic/paper-g1-and-mcc/blob/}\\%
%    \texttt{89dc05e80432f727cc41f07ecfeda5c87e69945d/}%
%\texttt{mcc-proof/MCC\_atTop\_eq\_FM/WuAristotle.lean}}

%%** TODO: Add sha256 checksum **

%\item IPFS snapshot (CID): \\
%\href{https://ipfs.io/ipfs/bafybeihfg46sgh2bg2fy3rph5wjdzgwcrxufph2w6vd35isz2rhbvvibpu}{%
%\texttt{https://ipfs.io/ipfs/}%
%\texttt{bafybeihfg46sgh2bg2fy3rph5wjdzgwcrxufph2w6vd35isz2rhbvvibpu}}
%\end{itemize}

%%# Aristotle version
%%bafybeihfg46sgh2bg2fy3rph5wjdzgwcrxufph2w6vd35isz2rhbvvibpu

%%# GPT 5.1 version
%%bafkreihwpqlr3s2mcu6csopndx3pvpo5az7m66iw5ox4lnqk7i3jjihnky


%The GitHub permalink fixes the exact commit, and the IPFS CID fixes the exact
%file content, providing redundancy against link rot and build-in checksum
%verification.


%%% ---------------

% Old L'Hôpital argument

%We can take the limit of this equation using using L'Hôpital's rule --- \ie{}
%the limit is equal to the limit of the derivative of the numerator with respect
%to \TN{} divided by the limit of the denominator with respect to \TN{}.

%\begin{equation}
%    = \lim_{\TN{} \to \infty}
%    \frac{
%        \frac{\partial \TP{} \cdot \TN{} - \FP{} \cdot \FN{}}{\partial \TN{}} 
%    }
%    {
%        \frac{\partial \sqrt{(\TP{} + \FP{}) (\TP{} + \FN{}) (\TN{} + \FP{}) (\TN{} + \FN{})}}{\partial \TN{}}
%    } 
%\end{equation}

%The derivative of the numerator simplifies to $\TP{}$ by applying the product
%rule. The derivative of the denominator can be taken using the chain rule and
%product rules. Explicitly showing this process is not too difficult, but it is
%involved. For conciseness we omit the explicit steps and compute the derivative
%symbolically using a computer. Taking the derivative of the numerator and
%denominator we get:

%\begin{equation}
%    = \lim_{\TN{} \to \infty}
%    \frac{
%        \TP{} 
%    }
%    {
%        \sqrt{
%            \frac{
%                (\FN{} + \TN{}) (\FN{} + \TP{}) (\FP{} + \TP{})
%            }{
%                4 (\FP{} + \TN{})
%            }} + 
%        \sqrt{
%            \frac{
%                (\FP{} + \TN{}) (\FN{} + \TP{}) (\FP{} + \TP{})
%            }{
%                4 (\FN{} + \TN{})
%            }
%        }
%    }
%\end{equation}

%In the limit the terms with \TN{} cancel, resulting in:


%\begin{equation}
%    =
%    \frac{
%        \TP{} 
%    }
%    {
%        \frac{
%            \sqrt{(\FN{} + \TP{}) (\FP{} + \TP{})}
%        }{
%            2 
%        } + 
%        \frac{
%            \sqrt{(\FN{} + \TP{}) (\FP{} + \TP{})}
%        }{
%            2 
%        }
%    } 
%\end{equation}


