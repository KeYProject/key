public class Test {
	//@ ghost int t;

	/*@ public normal_behaviour
	  @ requires true;
	  @*/
	public void test(int t) {
		//@ set this.t = t;
	}
}