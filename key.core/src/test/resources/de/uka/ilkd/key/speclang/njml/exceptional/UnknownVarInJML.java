// exceptionClass: BuildingException
// msgContains: Cannot resolve 'unknownVar'
// position: 9/18


class UnknownVar {

    /*@ public normal_behaviour
      @  ensures unknownVar == 42;
      @*/
    public void m() {}
}
