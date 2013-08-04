
public class ConstructorTest {
	private int value;
	
	/*@
	  @ ensures value == 42 - 4711;
	  @*/
	public ConstructorTest(int x, B a) {
		value = a.magic() + a.staticMagic();
	}
}
