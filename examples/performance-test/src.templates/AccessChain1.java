class AccessChain1 {
  AccessChain1 a;
  int x;
  int y;


  //@ requires a != null;
  //@ requires a.x > 0;
  //@ ensures a.x > 0;
  void foo_1() {
    a.x++; bar();
  }


  //@ requires a != null;
  //@ requires a.x > 0;
  //@ ensures a.x > 0;
  void foo_2() {
    a.x++; bar();
    a.x++; bar();
  }


  //@ requires a != null;
  //@ requires a.x > 0;
  //@ ensures a.x > 0;
  void foo_4() {
    a.x++; bar();
    a.x++; bar();
    a.x++; bar();
    a.x++; bar();
  }


  //@ requires a != null;
  //@ requires a.x > 0;
  //@ ensures a.x > 0;
  void foo_8() {
    a.x++; bar();
    a.x++; bar();
    a.x++; bar();
    a.x++; bar();
    a.x++; bar();
    a.x++; bar();
    a.x++; bar();
    a.x++; bar();
  }


  //@ ensures true;
  //@ assignable y;
  void bar () {};

}
