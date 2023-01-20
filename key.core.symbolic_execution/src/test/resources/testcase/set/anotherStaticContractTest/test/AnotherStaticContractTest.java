
public class AnotherStaticContractTest {
	public static int main(int x) {
		return magic(x);
	}
	
	/*@ normal_behavior
	  @ requires x >= 10;
	  @ ensures \result == 10;
	  @ also
	  @ normal_behavior
	  @ requires x < -22;
	  @ ensures \result == -22;
	  @ also
	  @ exceptional_behavior
	  @ requires x == 4;
	  @ also
	  @ requires x == -3;
	  @ ensures \result == -3;
	  @ also
	  @ behavior
	  @ ensures \result == 4711;
	  @*/
	public static int magic(int x) {
		return 42;
	}
}
