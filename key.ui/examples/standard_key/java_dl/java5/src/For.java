final class For implements Iterable {

  // This example has been refactored pending solution to bug #1288
  Trivial it;

  //@ ensures \result == (\sum int j; 0 <= j && j < a.length; a[j]);
  int sum (int[] a) {
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
  void infiniteLoop(For f) {
    //@ maintaining \invariant_for(f);
    //@ assignable \strictly_nothing;
    for (Object o: f);
  }

  java.util.Iterator iterator () { return it; } 

  final class Trivial extends java.util.Iterator {
    boolean hasNext() { return true; }
    Object next() { return null; }
  }
}
