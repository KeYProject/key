class IntTriple {
    // abstract state
    //@ ghost int x;
    //@ ghost \dl_IntPair yz;                     // default value is needed here!
    int a, b, c;        // concrete state


    // coupling invariant
    //@ invariant a == x && \dl_fst(yz) == b && \dl_snd(yz) == c;

    //@ ensures yz == \dl_ip(0,0);      // (auto) provable
    IntTriple() {
    }

    /*@ normal_behavior
      @  requires true;
      @  ensures \result == \dl_fst(yz);   // (auto) provable
      @  assignable \nothing;
      @*/
    int getSecond() {
        return b;
    }
}
