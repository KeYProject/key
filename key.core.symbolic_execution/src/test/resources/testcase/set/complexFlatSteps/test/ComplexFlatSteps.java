
public class ComplexFlatSteps {
	/* Start
	 * self.doSomething()
	 * int x = 1 + 2;
	 * int y = 2 * 4 * 9;
	 * int z = 3 * (4 / (2 - 3));
	 * return
	 * <endNode>
	 */
	
	/*@ requires true;
	  @ ensures true;
	  @*/
	public void doSomething() {
		int x = 1 + 2;
		int y = 2 * 4 * 9;
		int z = 3 * (4 / (2 - 3));
	}
}
