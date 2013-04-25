class Inc2 {
  int x;
  int y;


  //@ requires x > 0;
  //@ ensures x > 0;
  void foo () {
    x++; y++;
  }


  //@ ensures true;
  //@ assignable y;
  void bar () ;

}
