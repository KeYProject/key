public class Test {

    //@ public normal_behaviour
    //@ ensures true;
    public void test() {
        List l = new ArrayList();
        l.add(23);
        assert l.get(0) == 23;
        l.add(42);
        assert l.get(0) == 23;
        assert l.get(1) == 42;

        List l2 = new ArrayList();
        l2.add(100);
        assert l2.get(0) == 100;
        assert l.get(0) == 23;
        assert l.get(1) == 42;
    }

}
