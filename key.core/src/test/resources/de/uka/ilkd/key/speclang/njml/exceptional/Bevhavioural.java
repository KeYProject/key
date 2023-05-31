// exceptionClass: ConvertException
// msgContains: no viable alternative at input 'normal_bevhaviour
// position: 14/16
// verbose: true
// broken: true

// This is broken since it currently reports the wrong location

// There used to be an NPE
//   Caused by: java.lang.NullPointerException: Cannot read field "second" because "pos" is null

class Bevhavioural {

    /*@ public normal_bevhaviour
      @  ensures true;
      @*/
    public void m() {}
}
