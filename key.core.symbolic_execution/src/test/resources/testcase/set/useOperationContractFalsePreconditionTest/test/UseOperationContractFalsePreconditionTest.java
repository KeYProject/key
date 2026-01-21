
public class UseOperationContractFalsePreconditionTest {
	public static int main() {
		int magicNumber = magic(123);
		int magicNumberCopy = magicNumber;
		return magicNumber + magicNumberCopy;
	}
	
	/*@ public normal_behavior
	  @ requires false;
	  @ ensures \result == 42;
	  @*/
	public static int magic(int x) {
		return 42;
	}
}
