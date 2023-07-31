// exceptionClass: BuildingException
// msgContains: The fully qualified name 'unknownVar' could not be resolved.
// position: 9/18


class UnknownVar {

    /*@ public normal_behaviour
      @  ensures unknownVar == 42;
      @*/
    public void m() {}
}
