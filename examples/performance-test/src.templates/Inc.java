class Inc {
  int x;
  int y;


  //@ requires x > 0;
  //@ ensures x > 0;
  void foo () {
    x++;
  }


  //@ ensures true;
  //@ assignable y;
  void bar () {};

}
