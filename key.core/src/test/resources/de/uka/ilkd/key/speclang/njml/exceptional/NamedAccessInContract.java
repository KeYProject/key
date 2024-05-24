// position: 12/20
// verbose: true
// broken: true
// noException: false

// Originally, the problem was: currently does not report an exception

class NamedAccessInContract {

    /*@ public normal_behaviour
      @  accessible \inv : \everything;
      @*/
    /*@ pure */int m() { return 0; }
}
