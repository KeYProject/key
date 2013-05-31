class ForReferenceArray {

  //@ ensures true;
  void foo(Object[] as) {
    //@ maintaining 0 <= \index && \index <= as.length; 
    //@ decreasing as.length-\index;
    //@ assignable \strictly_nothing;
    for (Object a: as) ;
  }
}
