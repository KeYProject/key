//TODO
// The contracts below are not provable on the exploration branch.
// This is because when applying a method contranct, the formal parameters are not correctly replaced by the actual parameters.
// -- lanzinger
public class Bug {
    
    /*@ normal_behavior
      @ requires a >= 0;
      @*/
    public static void caller(int a) {
        callee(a);
    }
    
    /*@ normal_behavior
      @ requires count >= 0;
      @*/
    public static void callee(int count) { }
}
