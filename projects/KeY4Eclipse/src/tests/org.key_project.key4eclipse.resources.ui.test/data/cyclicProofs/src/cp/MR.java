package cp;

/**
 *
 * @author christoph
 */
public class MR {

    //@ public normal_behavior ensures false;
    public void a() {
        b();
    }

    //@ public normal_behavior ensures false;
    public void b() {
        a();
    }
}
