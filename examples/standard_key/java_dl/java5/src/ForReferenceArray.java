class ForReferenceArray {

  Object[] as;

  //@ ensures true;
  void foo() {
    //@ maintaining 0 <= \index && \index <= as.length; 
    //@ decreasing as.length-\index;
    //@ assignable \strictly_nothing;
    for (Object a: as) ;
  }
}
