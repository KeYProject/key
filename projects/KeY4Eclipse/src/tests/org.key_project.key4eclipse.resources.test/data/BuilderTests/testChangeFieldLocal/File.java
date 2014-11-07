
public class File {
	
	int field = 0;

	/*@
	  @ ensures \result == x + y;
	  @*/
	public int add(int x, int y) {
		return x + y + field;
	}
}
