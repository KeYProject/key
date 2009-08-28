class MySubclass extends MyClass {
    
    int add27(int i) {
	return attr = 27 + i;
    }
    
    
    
    MyClass mc;
    //@ invariant mc.<inv>;   
    
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
    
    
    /*@ assignable this.*;
      @ ensures modelField == \old(modelField) + 2;
      @*/
    void changeModelField() {
	x++;
	y++;
    }   
}