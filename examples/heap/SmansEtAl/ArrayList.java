class ArrayList {
    private int count;
    private /*@nullable@*/Object[] items;
    
    /*@ model \set footprint;
      @ accessible footprint: footprint;
      @ represents footprint <- count, items, items[*], items.length;
      @*/
    
    
    /*@ invariant items != null;
      @ invariant 0 <= count && count <= items.length;
      @ invariant \typeof(items) == \type(Object[]);
      @ accessible <inv>: footprint;
      @*/
    
    
    /*@ assignable \nothing;
      @ ensures size() == 0;
      @ ensures \fresh(footprint);
      @*/
    ArrayList() {
	items = new Object[10];
    }
    
    
    /*@ assignable footprint;
      @ ensures size() == \old(size()) + 1;
      @ ensures get(size() - 1) == o;
      @ ensures (\forall int i; 0 <= i && i < size() - 1; get(i) == \old(get(i)));
      @ ensures \newElemsFresh(footprint);
      @*/
    void add(Object o) {
	if(count == items.length) {
	    Object[] temp = new Object[count + 10];
	    /*@ loop_invariant 0 <= i && i <= count
	      @    && (\forall int x; 0 <= x && x < i; temp[x] == items[x]);
	      @ assignable temp[*];
	      @*/
	    for(int i = 0; i < count; i++) {
		temp[i] = items[i];
	    }
	    items = temp;
	}
	items[count++] = o;
    }
    
    
    // @ accessible get: footprint; 
    /*@ requires 0 <= i && i <= size();
      @ assignable \nothing;
      @ ensures \result == get(i);
      @*/
    Object get(int i) {
	return items[i];
    }

    
    //@ accessible size(): footprint;
    /*@ ensures \result == size();
      @*/
    int size() {
	return count;
    }
}
