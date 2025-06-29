class Quantor {
    /*@ normal_behaviour
      @ requires -10 <= n < 10;
      @ measured_by n;
      @ ensures \result >= 0;
      @*/
    int square1(int n) {
        //@ assert (\forall int i; -10 <= i < 10; i*i >= 0);
        return n*n;
    }
    /*@ normal_behaviour
      @ requires -10 <= n < 10;
      @ measured_by n;
      @ ensures \result >= 0;
      @*/
    int square2(int n) {
        //@ assume (\forall int i; -10 <= i < 10; i*i >= 0);
        return n*n;
    }
}
