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
	return new ArrayListIterator(this);
    }
    
    
    public int size() {
	return size;
    }
        
    //interactive proofs:
    //-contains (obvious quantifier instantiation)
    
    
    
    //inner class--------------------------------------------------------------
    
    private static class ArrayListIterator implements ListIterator {
	private final ArrayList arrayList; //workaround; should be ArrayList.this
	private int arrayPos = 0;
	
	//@ represents list <- arrayList;
	//@ represents pos <- arrayPos;
	
	//@ invariant arrayList.<inv>;
	//@ invariant 0 <= arrayPos && arrayPos <= arrayList.size;
	//@ invariant \typeof(arrayList) == ArrayList;
	
	/*@ normal_behaviour
	  @   requires l.<inv> && \typeof(l) == ArrayList;
	  @   ensures list == l;
	  @   ensures pos == 0; 
	  @*/
	public /*@pure@*/ ArrayListIterator(ArrayList l) {
	    arrayList = l;
	}
	
	
	public boolean hasNext() {
	    return arrayPos < arrayList.size;
	}
    
	
	public Object next() {
	    if(arrayPos == arrayList.size) {
		throw new IndexOutOfBoundsException();
	    }
	    arrayPos++;
	    return arrayList.array[arrayPos - 1];
	}
    }
}
