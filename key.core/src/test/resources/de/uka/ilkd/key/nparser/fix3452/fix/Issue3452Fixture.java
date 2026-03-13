class A {
    /*@ public model_behaviour
      @   requires n >= 0;
      @   ensures \result.length == n;
      @   measured_by n;
      @ public no_state static model \seq b(\bigint n) {
      @   return n == 0 ? \seq_empty : \seq_concat(b(n-1), \seq(0));
      @ }
      @*/

    /*@ public model_behaviour
      @   requires n >= 0;
      @   ensures \result.length == n;
      @   accessible \nothing;
      @   measured_by n;
      @ public static model \seq c(\bigint n) {
      @   return n == 0 ? \seq_empty : \seq_concat(c(n-1), \seq(0));
      @ }
      @*/

    int someHeapField;

    //@ ensures true;
    void m() {
        //@ ghost \seq x = c(5);
        someHeapField = 42;
        //@ assert x == c(5);
    }

}
