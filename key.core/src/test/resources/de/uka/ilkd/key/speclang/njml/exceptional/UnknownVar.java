// exceptionClass: PosConvertException
// msgContains: Could not resolve FieldReference "unknownVar"
// position: 12/9


class UnknownVar {

    /*@ public normal_bevhaviour
      @  ensures true;
      @*/
    public void m() {
        unknownVar = 42;
    }
}
