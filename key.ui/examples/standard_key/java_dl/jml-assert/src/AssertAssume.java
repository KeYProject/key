public class AssertAssume {
	/*@ public normal_behavior
	      ensures true;
	@*/
	public int singleAssumeAssert(int x) {
		//@ assume x == 0;
		//@ assert x != 1;
		return x;
	}
	/*@ public normal_behavior
	      ensures true;
	@*/
	public int singleAssertAssume(int x) {
		//@ assert x != 1;
		//@ assume x == 0;
		return x;
	}
        /* ... */
}
