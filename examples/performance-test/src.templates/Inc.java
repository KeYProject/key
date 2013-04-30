class Inc {
  int x;


  //@ requires x > 0;
  //@ ensures x > 0;
  void foo () {
    x++;
  }

}
