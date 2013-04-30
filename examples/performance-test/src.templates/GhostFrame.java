class GhostFrame {
  int x;
  int y;

  //@ ghost \locset footprint;

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo () {
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
  }


  //@ ensures \disjoint(footprint,\singleton(x));
  //@ assignable footprint;
  void bar () {};

}
