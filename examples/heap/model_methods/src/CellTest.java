class CellTest {

    /*@ requires c.<inv>; ensures c.post_set(x); @*/
    void callSet(Cell c, int x) {
        c.set(x);
    }

    /*@ requires r.<inv>; ensures r.get() == 5; @*/
    void test(Recell r) {
        r.set(5);
        callSet(r, 4);
        r.undo();
    }

}