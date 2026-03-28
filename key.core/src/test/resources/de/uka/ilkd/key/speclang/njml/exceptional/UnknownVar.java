// exceptionClass: ParserException
// msgContains: Name could not be resolved 'unknownVar'
// position: 12/9


class UnknownVar {

    /*@ public normal_behaviour
      @  ensures true;
      @*/
    public void m() {
        unknownVar = 42;
    }
}
