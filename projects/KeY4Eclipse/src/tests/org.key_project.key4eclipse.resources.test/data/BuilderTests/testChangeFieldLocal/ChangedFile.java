
public class File {
	
	int field = 1;

	/*@
	  @ ensures \result == x + y;
	  @*/
	public int add(int x, int y) {
		return x + y + field;
	}
}
