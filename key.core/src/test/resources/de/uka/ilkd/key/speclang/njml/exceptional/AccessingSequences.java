// verbose: true
// broken: true
// xxxexceptionClass: PosConvertException
// xxxmsgContains: XXXX

class AccessingSequences {

    //@ ghost \seq seq;
    
    //@ ensures \result == seq[null];
    int m() { }
}

// Is there positioning information?
