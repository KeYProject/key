class Stack {
    private ArrayList contents;
    
    
    /*@ assignable \nothing;
      @ ensures size() == 0;
      @ ensures \fresh(footprint);
      @*/
    Stack() {
	contents = new ArrayList();
    }
    

    /*@ assignable footprint;
      @ ensures size() == \old(size()) + 1;
      @ ensures \newElemsFresh(footprint);
      @*/
    void push(/*@nullable@*/ Object o) {
	contents.add(o);
    }
    
    
    /*@ assignable \nothing;
      @ accessible footprint;
      @ ensures \result == size();
      @*/
    int size() {
	return contents.size();
    }
    
    
    /*@ depends <inv>: footprint;
      @ invariant contents.<inv>;
      @ invariant \disjoint(contents, contents.footprint);
      @*/
    
    
    /*@ model \set footprint;
      @ depends footprint: footprint;
      @ represents footprint <- contents, contents.footprint;
      @*/
}
