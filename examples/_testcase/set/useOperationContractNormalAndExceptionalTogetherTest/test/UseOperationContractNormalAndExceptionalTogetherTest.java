
public class UseOperationContractNormalAndExceptionalTogetherTest {
	/*@ public normal_behavior
	  @ ensures \result == 42 * 2;
	  @*/
	public static int main() {
		try {
			int magicNumber = magic(123);
			int magicNumberCopy = magicNumber;
			return magicNumber + magicNumberCopy;
		}
		catch (Exception e) {
			return -1;
		}
	}
	
	/*@ public normal_behavior
	  @ requires x >= 0;
	  @ ensures \result == 42;
	  @
	  @ also
	  @
	  @ public exceptional_behavior
	  @ requires x < 0;
	  @ signals (Exception myExc) \not_specified;
	  @*/
	public static int magic(int x) throws Exception {
		if (x >= 0) {
			return 42;
		}
		else {
			throw new Exception();
		}
	}
}
