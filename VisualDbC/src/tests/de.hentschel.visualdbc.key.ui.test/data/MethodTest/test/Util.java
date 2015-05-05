
public class Util {
	/*@
	  @ ensures \result == 42;
	  @*/
	public static int getMagic() {
		return 42;
	}
	
	/*@
	  @ ensures \result == a + b;
	  @*/
	public static int add(int a, int b) {
		return a + b;
	}
   
   /*@
     @ ensures true;
     @*/
   public void unusedMethod() {
   }
}
