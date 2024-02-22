// verbose: true
// broken: true
// msgContains: expecting an integer value, not null

class AccessingSequences {

    //@ ghost \seq seq;
    
    //@ ensures \result == seq[null];
    int m() { }
}

// Is there positioning information?

/* Not so helpful error message:

Building a term failed. Normally there is an arity mismatch or one of the subterms' sorts is not compatible (e.g. like the '2' in "true & 2")
The top level operator was any::seqGet(Sort: any); its expected arg sorts were:
1.) sort: Seq, sort hash: 1884170567
2.) sort: int, sort hash: 1928174253
 */