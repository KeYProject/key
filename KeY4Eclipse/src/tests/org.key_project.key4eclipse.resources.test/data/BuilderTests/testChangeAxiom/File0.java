
public class File0 {

	//@ public invariant i == 0; 

	int i = 0;
	
	/*@
	  @ ensures \result == x + y;
	  @*/
	public int add(int x, int y) {
		return x + y - i;
	}
	
	/*@
	  @ ensures \result == x - y;
	  @*/
	public int sub(int x, int y) {
		return x - y + i;
	}
}
