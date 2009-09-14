class CellClient {
    
    //@ ensures \result == 5;
    int m() {
	Cell c1 = new Cell();
	c1.setX(5);
	
	Cell c2 = new Cell();
	c2.setX(10);
	
	return c1.getX();
    }
}
