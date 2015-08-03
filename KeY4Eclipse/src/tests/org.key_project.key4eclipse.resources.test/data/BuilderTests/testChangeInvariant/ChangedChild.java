
public class Child {
	/*@
	  @ public invariant x >= 2 && x <= 10;
	  @*/
	public int x;
	
	//@ ensures \result == x + y;
	public int add(int x, int y){
		return x + y;
	}
}
