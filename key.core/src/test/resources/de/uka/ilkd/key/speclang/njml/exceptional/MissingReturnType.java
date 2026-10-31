// exceptionClass: ProofInputException
// msgContains: Encountered unexpected token
// verbose: true


class MissingReturnType {

    /*@ public model_behaviour
      @  ensures \result == 1;
      @ model modelFct() { return 1; }
      @*/
}
