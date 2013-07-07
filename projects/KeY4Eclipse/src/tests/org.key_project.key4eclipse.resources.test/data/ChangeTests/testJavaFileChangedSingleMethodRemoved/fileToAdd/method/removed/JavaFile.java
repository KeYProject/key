package method.removed;

public class JavaFile {
	/*@
	  @ ensures \result == x + y;
	  @*/
	public static int add(int x, int y) {
		return x + y;
	}
	
	/*@
     @ ensures \result == x - y;
     @*/
	public static int sub(int x, int y) {
    return x - y;
 }
 
   /*@
     @ ensures \result == x * y;
     @*/
   public static int mul(int x, int y) {
      return x * y;
   }
}
