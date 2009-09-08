class MyClient {
    
    MyClass mc;
    //@ invariant mc.<inv> && \disjoint(this.*, mc.footprint);
    
    int i;
    
    
    //@ assignable i;
    void changingIPreservesInv() {
	i++;
    }
    

    /*@ assignable i, mc.footprint;
      @ ensures \result == 388;
      @*/
    int useContract() {
	i = 360;
	i = mc.add27(++i);
	return i;
    }
}
