class Test {    
    
    Cell c, c2;
    
    //@ ensures \disjoint(c.footprint, this.*);
    //@ ensures \disjoint(c.footprint, c2.footprint);    
    void test() {
       c = new Cell();
       c2 = new Cell();
    }
    
    //@ requires \disjoint(c2.footprint, this.*);
    //@ ensures \disjoint(c.footprint, this.*);
    //@ ensures \disjoint(c.footprint, c2.footprint);    
    void test2() {
        c = new Cell();
        c.setX(5);
    }
    
    
    //@ requires \disjoint(c2.footprint, this.*);
    //@ ensures \disjoint(c.footprint, this.*);
    // @ ensures \disjoint(c.footprint, c2.footprint);          //<---- DAS PROBLEM
    void test3() {
	c = new Cell();
        c.setX(5);
        c.setX(1);
    }
}
