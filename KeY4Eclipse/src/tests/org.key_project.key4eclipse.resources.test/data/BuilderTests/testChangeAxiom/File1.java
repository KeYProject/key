
public class File1 {
	/*@
	  @ ensures \result == x + y;
	  @*/
	public int add(int x, int y) {
		return x + y;
	}
	
	/*@
	  @ ensures \result == x - y;
	  @*/
	public int sub(int x, int y) {
		return x - y;
	}
}
