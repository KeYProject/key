public class SomeClass{ 

    public static SomeClass _instance;

    /*@ public normal_behavior
      @  assignable _instance;
      @  working_space 0;
      @  ensures \result==\old(_instance) && _instance==null;
      @*/
    public static SomeClass clear(){
	SomeClass old = _instance;
	_instance = null; 
	return old;
    }
    
    /*@ public normal_behavior
      @  requires _instance == null;
      @  assignable _instance;
      @  working_space \space(new SomeClass());
      @//  ensures \result==_instance && _instance!=null;
      @ also public normal_behavior
      @  requires _instance != null;
      @  assignable \nothing;
      @  working_space 0;  
      @//  ensures \result==\old(_instance);
      @*/
    public static SomeClass getInstance(){
	if(_instance==null) _instance = new SomeClass();
	return _instance;
    }

    /*@  requires _instance!=null;
      @//  assignable _instance;
      @//  ensures \old(_instance) != _instance &&
      @//          \result == _instance &&
      @//          \result != null;
      @  working_space \working_space(clear()) +
      @                \working_space_rigid(getInstance(), 
      @                                     SomeClass._instance==null); 
      @*/
    public SomeClass freshInstance(){
	clear();
	return getInstance();
    }

}
