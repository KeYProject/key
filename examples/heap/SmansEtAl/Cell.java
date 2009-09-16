class Cell {
    private int x;
    
    /*@ model \set footprint;
      @ accessible footprint: footprint;
      @ represents footprint <- x;
      @*/
        
    /*@ assignable \nothing;
      @ ensures getX() == 0;
      @ ensures \fresh(footprint);
      @*/
    /*@helper@*/ Cell() {
    }
    
    
    //@ accessible getX(): footprint;
    /*@ assignable \nothing;
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
}
