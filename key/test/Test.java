class Test {
    /*@ public model_behaviour
      @     requires true;
      @     static model boolean test(int value) {
      @     return
      @         0 <= value;
      @ }
      @*/


    public static final int CONST = 42;
    //@ensures \result == 42;
    public int foo() {return CONST;}
}