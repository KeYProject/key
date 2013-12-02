interface Coll {

    /*@ model_behavior
      @ ensures x>0 ==> \result;
      @ model boolean addPre(int x);
      @*/

    //@ requires addPre(x);
    void add(int x);
}

class Indirect {
    /*@ requires c.addPre(v); @*/
    void callAdd(Coll c, int v) {
        c.add(v);
    }

    //@ ensures true;
    void test(Coll1 c1, Coll2 c2) {
        callAdd(c1, 42);
        callAdd(c2, -42);
    }
}

class Coll1 implements Coll {

    /*@ model boolean add_pre(int x) { return (x > 0); } @*/

    void add() { }

}


final class Coll2 implements Coll { 

    /*@ model boolean add_pre(int x) { return true; } @*/

    void add() { }

}