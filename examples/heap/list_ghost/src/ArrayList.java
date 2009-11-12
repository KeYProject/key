final class ArrayList implements List {
    
    private /*@nullable@*/ Object[] array = new Object[10];
    private int size = 0;
    
    //@ invariant footprint == \setUnion(this.*, array.*);                                      
    
    //@ invariant array != null;
    //@ invariant 0 <= size && size <= array.length;
    //@ invariant \typeof(array) == \type(Object[]);
    
    /*@ normal_behaviour
      @   ensures size() == 0;
      @   ensures \fresh(footprint);
      @*/
    public /*@pure@*/ ArrayList() {
	//@ set footprint = \setUnion(\allFields(this), \allFields(array)); 
    }
    
    
    /*@ normal_behavior
      @   assignable array, \singleton(footprint);
      @   ensures \fresh(array);
      @   ensures array.length > \old(array.length);
      @   ensures (\forall int x; 0 <= x && x < size; array[x] == \old(array[x]));
      @*/
    private void enlarge() {
	final Object[] newArray = new Object[array.length + 10];
	
	/*@ loop_invariant 0 <= i && i <= size 
	  @  && (\forall int x; 0 <= x && x < i; newArray[x] == array[x]);
	  @ assignable newArray[*];
	  @*/
	for(int i = 0; i < size; i++) {
	    newArray[i] = array[i];
	}
	array = newArray;
	//@ set footprint = \setUnion(\allFields(this), \allFields(array));
    }
        

    public void add(Object o) {
	if(size == array.length) {
	    enlarge();
	}
	array[size++] = o;
    }

    
    public Object get(int index) {
	if(index < 0 || size <= index) {
	    throw new IndexOutOfBoundsException();
	}
	return array[index];
    }
    
    
    public int size() {
	return size;
    }
}
