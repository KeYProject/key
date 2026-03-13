// noException: true
// broken: true
class NoState {

    /*@ public model_behaviour
      @  ensures \result == 1;
      @ model no_state int modelFct() { return 1; }
      @*/
}

// Strange error message: 'Lexical error at line 11, column 38.  Encountered: <EOF> after : ""'