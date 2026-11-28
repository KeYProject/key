// exceptionClass: BuildingException
// msgContains: Cannot resolve 'unknownVar'


class UnknownVar {

    /*@ public normal_behaviour
      @  ensures unknownVar == 42;
      @*/
    public void m() {}
}
