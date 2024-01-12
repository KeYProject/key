final class For implements Iterable {

    int[] a;
    Trivial it;
    For f;

    //@ ensures \result == (\sum int j; 0 <= j && j < a.length; a[j]);
    int sum () {
        int s = 0;
        int z = a.length;

        /*@ maintaining s == (\sum int j; 0 <= j && j < \index; a[j]);
          @ maintaining 0 <= \index && \index <= a.length;
          @ decreasing a.length - \index;
          @ assignable \strictly_nothing;
          @*/
        for (int i: a) s+= i;
        return s;
    }

    /*@ requires \invariant_for(f);
      @ diverges true;
      @ ensures false;
      @*/
    void infiniteLoop() {
        //@ maintaining \invariant_for(f);
        //@ assignable \strictly_nothing;
        //disabled //@ diverges true;
        //   this would remove the syntax warning, but triggers other strange
        //   behaviour cases (and is not traditional Java)
        for (Object o: f);
    }

    public Trivial iterator () { return it; }

    final class Trivial implements java.util.Iterator {
        public boolean hasNext() { return true; }
        public Object next() { return null; }
        public void remove() { }
    }
}
