// exceptionClass: ParserException
// msgContains: Could not resolve FieldReference "unknownVar"
// position: 12/9


class UnknownVar {

    /*@ public normal_behaviour
      @  ensures true;
      @*/
    public void m() {
        unknownVar = 42;
    }
}
