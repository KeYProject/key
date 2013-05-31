
public class UseOperationContractNormalAndExceptionalBranchTest {
	public static int main(int value) {
		try {
			int magicNumber = magic(value);
			int magicNumberCopy = magicNumber;
			return magicNumber + magicNumberCopy;
		}
		catch (Exception e) {
			return -1;
		}
	}
	
	/*@ public normal_behavior
	  @ requires x >= 0 && x < 10;
	  @ ensures \result == 42;
	  @
	  @ also
	  @ public normal_behavior
	  @ requires x >= 10;
	  @ ensures \result == 84;
	  @
	  @ also
	  @
	  @ public exceptional_behavior
	  @ requires x < 0 && x >= -10;
	  @ signals (Exception myExc) \not_specified;
	  @
	  @ also
	  @
	  @ public exceptional_behavior
	  @ requires x < -10;
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
