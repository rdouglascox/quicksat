# quicksat

just some utilities for benchmarking logic sat checkers and for experimenting with various sat checking algorithms, many of which will be based on semantic tablueax.

benchmarking is provided by the criterion library. 

i am mainly interested here in quick sat checkers for moderately small inputs. most sat checkers are optimised for dealing with large inputs. this is because my use case for the sat checkers is finding suitable propositions for undergraduate logic questions and my search method is just to test a random stream of propositions until a suitable proposition is found.

i am interested in two kinds of sat checkers here. one kind simple returns a Boolean result for whether the input propositions are satisfiable or not. another kind returns a logic-textbook proof tree or semantic tableaux.

