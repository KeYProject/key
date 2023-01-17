public class ModelMethods {
    /*@ public model_behaviour
      @ requires true;
      @ model static boolean testModelStatic() {
      @     return true;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ model boolean testModel() {
      @     return true;
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires true;
      @*/
    public static void test1() {
        //@ assert testModelStatic();
    }

    /*@ public normal_behaviour
      @ requires true;
      @*/
    public void test2() {
        //@ assert testModelStatic();
    }

    /*@ public normal_behaviour
      @ requires true;
      @*/
    public void test3() {
        //@ assert testModel();
    }

    /*@ public normal_behaviour
      @ requires true;
      @*/
    public static void test4() {
        ModelMethods t = new ModelMethods();
        //@ assert t.testModel();
    }
}
