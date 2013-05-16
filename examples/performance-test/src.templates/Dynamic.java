class Dynamic {
  int x;
  int y;

  //@ model \locset footprint;
  //@ accessible footprint: footprint;

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
  }


  //@ ensures \new_elems_fresh(footprint);
  //@ assignable footprint;
  void bar () {};

}
