// exceptionClass: PosConvertException
// msgContains: no viable alternative at input 'modelFct('
// position: 11/23
// verbose: true


class MissingReturnType {

    /*@ public model_behaviour
      @  ensures \result == 1;
      @ model modelFct() { return 1; }
      @*/
}
