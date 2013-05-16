class Dynamic2 {
  int x;
  int y;

  //@ model \locset rep;
  //@ accessible rep: rep;

  //@ model \locset rep2;
  //@ accessible rep2: rep2;

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo () {
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
  }


  //@ ensures \new_elems_fresh(rep2);
  //@ assignable rep2;
  void bar () {};

}
