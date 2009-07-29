class MyArrayList implements MyList {
    
    private Object[] array = new Object[10];
    private int size = 0;
    
    
    private void enlarge() {
	Object[] newArray = new Object[array.length + 10];
	
	/*@ loop_invariant 0 <= i && i <= size 
	  @  && (\forall int x; 0 <= x && x < i; newArray[x] == array[x]);
	  @ assignable i, newArray[*];
	  @*/
	for(int i = 0; i < size; i++) {
	    newArray[i] = array[i];
	}
	array = newArray;
    }
    
    
    public void add(Object element) {
	if(size >= array.length) {
	    enlarge();
	}
	array[size++] = element;
    }

    
    public Object get(int index) {
	return array[index];
    }
}
