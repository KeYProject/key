class AccessChain4 {
  AccessChain a;
  int x;
  int y;


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo () {
    a.a.a.a.x++; bar();
  }


  //@ ensures true;
  //@ assignable y;
  void bar () ;

}
