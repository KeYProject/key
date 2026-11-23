public class CastObject {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static void m() {
        Object o = (Object) 42;
        //@ assert o != null;
    }

    public static void main(String[] args) {
        m();
        System.out.println("object=nonnull");
    }
}
