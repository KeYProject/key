class CellTest {

    /*@ requires c.<inv>; ensures c.post_set(x) && c.<inv>; @*/
    void callSet(Cell c, int x) {
        c.set(x);
    }

    /*@ requires r.<inv>; ensures r.get() == 5; @*/
    void test(Recell r) {
        r.set(5);
        callSet(r, 4);
        r.undo();
    }

    /*@ requires c.<inv>; ensures c.get() == 4; @*/
    void test2(Cell c) {
        c.set(5);
        callSet(c, 4);
    }

}