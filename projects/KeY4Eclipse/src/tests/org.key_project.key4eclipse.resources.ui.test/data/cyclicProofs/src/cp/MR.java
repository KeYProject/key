package cp;

/**
 *
 * @author christoph
 */
public class MR {
    /*@ normal_behavior
      @ ensures true;
      @*/
    public MR() {
    }

    //@ public normal_behavior ensures false;
    public void a() {
        b();
    }

    //@ public normal_behavior ensures false;
    public void b() {
        a();
    }
}
