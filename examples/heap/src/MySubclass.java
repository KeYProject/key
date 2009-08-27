class MySubclass extends MyClass {
    
    int add27(int i) {
	return attr = 27 + i;
    }
    
    //@ normal_behavior
    //@  ensures \result == 27;
    static int test() {
	return 27;
    }
    
    
    MyClass mc;
    /*@ requires mc != null;
      @ assignable mc.attr;    
      @ ensures \result == 388;
      @*/
    int useContract() {
	int i = 360;
	i = mc.add27(++i);
	return i;
    }
}