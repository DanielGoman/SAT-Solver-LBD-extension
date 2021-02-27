# SAT-Solver-LBD-extension

Work done by Daniel Goman and David Galambos as a project in the course Algorithmic Logic.

In this project we received a cpp code of a working SAT solver written by the lecturer of the course - Prof. Ofer Strichman.

Our work features implemntation of an extension of the SAT solver, based on the work done in the paper "Predicting Learnt Clauses Quality in Modern SAT Solvers" by G. Audemard and L. Simon.

In their work, Audemard and Simor suggest a measure called LBD, which is an evaluation of the relevance of learned conflict clauses. They follow it up by designing a deletion mechanism which every so often delete some of the learned clauses based on this measure.

In our work we implement their idea, as well as we try to come up with heuristical improvements to the deletion rate of the learned clauses.

In this repository you could find the source code, as well as the test results of various versions of the code we wrote on a public dataset.

Link to the paper: 
https://www.ijcai.org/Proceedings/09/Papers/074.pdf
