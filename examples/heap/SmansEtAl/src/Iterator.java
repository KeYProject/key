class Iterator {
    private ArrayList list;
    private int index;
    
    
    /*@ requires l.<inv> && l.size() >= 0;
      @ assignable \nothing;
      @ ensures list() == l;
      @ ensures \fresh(footprint);
      @*/
    Iterator(ArrayList l) {
	list = l;
    }
    
    
    /*@ requires hasNext();
      @ assignable footprint;
      @ ensures list() == \old(list());
      @ ensures \newElemsFresh(footprint);
      @*/
    /*@nullable@*/ Object next() {
	return list.get(index++);
    }
    
    
    /*@ assignable \nothing;
      @ accessible footprint, list().footprint;
      @ ensures \result == hasNext();
      @*/
    boolean hasNext() {
	return index < list.size();
    }
    
    
    /*@ assignable \nothing;
      @ accessible footprint;
      @ ensures \result == list();
      @*/
    ArrayList list() {
	return list;
    }
    
    
    /*@ depends <inv>: footprint, list().footprint;
      @ invariant list.<inv>;
      @ invariant 0 <= index && index <= list.size(); 
      @ invariant \disjoint(this.*, list.footprint);
      @*/
    
    
    /*@ model \set footprint;
      @ depends footprint: footprint;
      @ represents footprint <- list, index;
      @*/    
}
