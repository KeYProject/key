final class ArrayList implements List {
    
    private /*@nullable@*/ Object[] array = new Object[10];
    private int size = 0;
    
    //@ represents footprint <- array, array[*], array.length, size;    
    
    //@ invariant array != null;
    //@ invariant 0 <= size && size <= array.length;
    //@ invariant \typeof(array) == \type(Object[]);
    
    
    /*@ normal_behaviour
      @   ensures size() == 0;
      @   ensures \fresh(footprint);
      @*/
    public /*@pure@*/ ArrayList() {
    }
    
    
    /*@ normal_behavior
      @   assignable array;
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
    }
        

    public void add(Object o) {
	if(size == array.length) {
	    enlarge();
	}
	array[size++] = o;
    }
    
    
    public boolean contains(Object o) {
	/*@ loop_invariant 0 <= i && i <= size
	  @  && (\forall int x; 0 <= x && x < i; array[x] != o);
	  @ assignable \nothing;
	  @*/
	for(int i = 0; i < size; i++) {
	    if(array[i] == o) {
		return true;
	    }
	}
	return false;
    }    

    
    public Object get(int index) {
	if(index < 0 || size <= index) {
	    throw new IndexOutOfBoundsException();
	}
	return array[index];
    }
    
    
    public ListIterator iterator() {
	return new ArrayListIterator();
    }
    
    
    public int size() {
	return size;
    }
        
    //interactive proofs:
    //-contains (obvious quantifier instantiation)
    
    
    
    //inner class--------------------------------------------------------------
    
    private class ArrayListIterator implements ListIterator {
	private int arrayPos = 0;
	
	//@ represents list <- ArrayList.this;
	//@ represents pos <- arrayPos;
	
	//@ invariant list.<inv>;
	//@ invariant 0 <= arrayPos && arrayPos <= list.size;
	//@ invariant \typeof(list) == ArrayList;
	
	
	public boolean hasNext() {
	    return arrayPos < ArrayList.this.size;
	}
    
	
	public Object next() {
	    if(arrayPos == ArrayList.this.size) {
		throw new IndexOutOfBoundsException();
	    }
	    arrayPos++;
	    return ArrayList.this.array[arrayPos - 1];
	}
    }
}
