// exceptionClass: Something
// msgContains: Unexepected
// location: xxxx
// verbose: true
// ignore: true

// This is ignored for the moment to allow the testing infrastructure to reach main. ...

// There used to be an NPE
//   Caused by: java.lang.NullPointerException: Cannot read field "second" because "pos" is null

class Bevhavioural {

    /*@ public normal_bevhaviour
      @  ensures true;
      @*/
    public void m() {}
}
