mod playground;
pub mod individual;

/*
    (1 - (q_last + q_blind)) * zp(wX) * Product_i(oracle(x) + sigma(x) + gamma) NOTE: second part is symmetrical 
    degree of this will always be: 
    2n - 2 + num_of_oracles * n - num_of_oracles

    so for num_of_oracles = 2 
        (1 - (q_last + q_blind)) * zp(wX) * (oracle1(x) + sigma1(x) + gamma) * (oracle2(x) + sigma2(x) + gamma)
        4n - 4

    for classic plonk arith we have qm * a * b - zh = 3n - 3 - n = 2n - 3
*/

/*

set u = 6

we want a * b - c = 0 



    a       b       c
------------------------
1   a1      b1      c1
------------------------
2
------------------------
3
------------------------
4
------------------------
5
------------------------
6
------------------------
7
------------------------
8

*/