class MySubclass extends MyClass {
    
    int add27(int i) {
	return i + 27;
    }
    
    //@ normal_behavior
    //@  ensures \result == 27;
    static int test() {
	return 27;
    }
    
    
    MyClass mc;
    /*@ requires mc != null;
      @ assignable attr, mc;    
      @ ensures attr == 27;
      @*/
    void useContract() {
	attr = 0;
	int i = MySubclass.test();//super.add27(attr);
	attr = i;
    }
}