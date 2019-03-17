
public class StaticDefaultContractTest {
	public static void main() {
		magic();
	}
	
	/*@ behavior
	  @ requires true;
	  @ ensures true;
	  @*/
	public static void magic() {
	}
}
