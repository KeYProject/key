public class MultipleRecursion {
    //@ public normal_behavior ensures false;
    public void a() {
        b();
    }

    //@ public normal_behavior ensures false;
    public void b() {
        a();
    }
}
