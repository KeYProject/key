class Cell {
    private int x;
    
    
    /*@ assignable \nothing;
      @ ensures getX() == 0;
      @ ensures \fresh(footprint);
      @*/
    Cell() {
    }
    
    
    /*@ assignable \nothing;
      @ accessible footprint;
      @ ensures \result == getX();
      @*/
    int getX() {
	return x;
    }
    
    
    /*@ assignable footprint;
      @ ensures getX() == value;
      @ ensures \newElemsFresh(footprint); 
      @*/
    void setX(int value) {
	x = value;
    }
    
    /*@ model \set footprint;
      @ depends footprint: footprint;
      @ represents footprint <- x;
      @*/
    
    //@ depends <inv>: \nothing;
}
