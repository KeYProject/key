// exceptionClass: PosConvertException
// msgContains: no viable alternative at input 'modelFct('
// position: 11/14
// verbose: true
// broken: true

class MissingReturnType {

    /*@ public model_behaviour
      @  ensures \result == 1;
      @ model modelFct() { return 1; }
      @*/
}
