// exceptionClass: PosConvertException
// msgContains: no viable alternative at input 'normal_bevhaviour
// verbose: true
// broken: false

// Originally, the problem was: This is broken since it currently reports the wrong location


class Bevhavioural {

    /*@ public normal_bevhaviour
      @  ensures true;
      @*/
    public void m() {}
}

// There used to be an NPE
//   Caused by: java.lang.NullPointerException: Cannot read field "second" because "pos" is null
