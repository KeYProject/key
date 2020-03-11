// This example has been refactored pending solution to bug #1288

final class For implements Iterable {

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
    java.util.Iterator it = f.iterator();
    
    //@ maintaining \invariant_for(f);
    //@ assignable \strictly_nothing;
    while (it.hasNext());
  }

  /*@ ensures \result instanceof java.util.CollectionIterator;
    @ ensures \invariant_for(\result);
    @ ensures \result.index < \result.seq.length;
    @*/
  java.util.Iterator iterator();
}
