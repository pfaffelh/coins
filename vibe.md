In Manuscript/20231006_p.tex on p. 2, you find the description of a game: You start with n coins, each coming up heads with probability p. In each round you have to set aside at least one coin. You win if eventually, all coins show heads. 

On p. 3, there are two strategies: 
(A): Always put aside exactly one coin (with head) if there is one, unless all are head. In this case, put aside all (and win).
(B) Always put aside as many coins as there are heads.

For p>1/2, it is shown in Lemma 0.3 that (A) is the best strategy. My goal is to 
1. get insights for the best strategy for p < 1/2
2. get bounds on p if (B) is the best strategy
3. obtain a closed form formula for the winning probability for strategy (B)

For context, consult 2406.14700v2.pdf on a different version of the game.





Please draft the skeleton for a Lean project. The most important point is to define w_{n,p} indictively using the Bellman equation. All our results are on this equation, right? As a first step, I want you to prove that for p=1/2, we find w_{n,1/2} = 1/2 for all n. And yes, of course, you should use mathlib! In a second step, implement the findings from halfp.tex. There, we proved that 