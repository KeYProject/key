// position: 12/20
// verbose: true
// broken: true
// exceptionClass: XXXX
// msgContains: XXXX

// currently does not report an exception

class NamedAccessInContract {

    /*@ public normal_behaviour
      @  accessible \inv : \everything;
      @*/
    /*@ pure */int m() { return 0; }
}
