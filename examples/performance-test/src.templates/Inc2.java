class Inc2 {
  int x;
  int y;

  //@ requires x > 0;
  //@ ensures x > 0;
  void foo_1 () {
    x++; y++;
  }

  //@ requires x > 0;
  //@ ensures x > 0;
  void foo_2 () {
    x++; y++;
    x++; y++;
  }

  //@ requires x > 0;
  //@ ensures x > 0;
  void foo_4 () {
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
  }

  //@ requires x > 0;
  //@ ensures x > 0;
  void foo_8 () {
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
  }

  //@ requires x > 0;
  //@ ensures x > 0;
  void foo_10 () {
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
  }

  //@ requires x > 0;
  //@ ensures x > 0;
  void foo_20 () {
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
  }

  //@ requires x > 0;
  //@ ensures x > 0;
  void foo_40 () {
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
    x++; y++;
  }


  //@ ensures true;
  //@ assignable y;
  void bar () {};

}
