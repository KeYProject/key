class MySubclass extends MyClass {
    
    MyClass mc;
    //@ invariant mc.<inv> && \disjoint(this.*, mc.footprint);
    
    //@ represents footprint <- this.*, mc.footprint;

    
    
    int add27(int i) {
	return attr = 27 + i;
    }
    
    
    /*@ assignable mc.attr;
      @ ensures \result == 388;
      @*/
    int useContract() {
	int i = 360;
	i = mc.add27(++i);
	return i;
    }
    
    
    
    //@ model int modelField;
    int x;
    int y;
    //@ represents modelField <- x + y;
    
    
    /*@ assignable x, y;
      @ ensures modelField == \old(modelField) + 2;
      @*/
    void changeModelField() {
	x++;
	y++;
    }   
}