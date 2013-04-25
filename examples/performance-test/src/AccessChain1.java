class AccessChain1 {
  AccessChain a;
  int x;
  int y;


  //@ requires a != null;
  //@ requires a.x > 0;
  //@ ensures a.x > 0;
  void foo () {
    a.x++; bar();
  }


  //@ ensures true;
  //@ assignable y;
  void bar () ;

}
