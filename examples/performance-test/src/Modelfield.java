class Modelfield {
  int x;
  int y;

  //@ model \locset footprint;
  //@ accessible footprint: \empty;

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo () {
    x++; bar();
  }


  //@ ensures true;
  //@ assignable footprint;
  void bar () ;

}
