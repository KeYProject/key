
public class SimpleStaticContractTest {
	public static int main(int x) {
		return magic(x);
	}
	
	/*@ normal_behavior
	  @ requires x >= 10;
	  @ ensures \result == 10;
	  @*/
	public static int magic(int x) {
		return 42;
	}
}
