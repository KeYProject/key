class Cell {
    private int x;
    
    
    /*@ assignable \nothing;
      @ ensures getX() == 0;
      @ ensures \fresh(footprint);
      @*/
    /*@helper@*/ Cell() {
    }
    
    
    /*@ assignable \nothing;
      @ accessible footprint;
      @ ensures \result == getX();
      @*/
    /*@helper@*/ int getX() {
	return x;
    }
    
    
    /*@ assignable footprint;
      @ ensures getX() == value;
      @ ensures \newElemsFresh(footprint); 
      @*/
    /*@helper@*/ void setX(int value) {
	x = value;
    }
    
    /*@ model \set footprint;
      @ depends footprint: footprint;
      @ represents footprint <- x;
      @*/    
}
