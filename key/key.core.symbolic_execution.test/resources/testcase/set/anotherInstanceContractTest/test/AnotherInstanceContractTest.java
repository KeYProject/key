
public class AnotherInstanceContractTest {
	public static int main(int x, AnotherInstanceContractTest obj) {
		return obj.magic(x);
	}
	
	/*@ normal_behavior
	  @ requires x >= 10;
	  @ ensures \result == 10;
	  @ also
	  @ normal_behavior
	  @ requires x < -22;
	  @ ensures \result == -22;
	  @*/
	public int magic(int x) {
		return 42;
	}
}
