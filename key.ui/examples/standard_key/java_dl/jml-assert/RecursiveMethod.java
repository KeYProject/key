// see https://git.key-project.org/key/key/-/issues/1669
class RecursiveMethod {
    /*@ normal_behaviour
      @ requires n >= 0;
      @ measured_by n;
      @ ensures \result >= 1;
      @*/
    int fac1(int n) {
        if(n==0) return 1;
        //@ assert true;
        return fac1(n-1)*n;
    }

    /*@ normal_behaviour
      @ requires n >= 0;
      @ measured_by n;
      @ ensures \result >= 1;
      @*/
    int fac2(int n) {
        if(n==0) return 1;
        //@ assume true;
        return fac2(n-1)*n;
    }
}
