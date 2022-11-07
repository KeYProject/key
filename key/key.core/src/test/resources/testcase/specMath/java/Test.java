public /*@ spec_java_math @*/ class Test {
	// This test uses casts from bigint to int being narrowing and requiring an explicit cast
	// Test failure is indicated by method resolution failing
	/*@ model_behaviour
	  @ requires true;
	  @ static model boolean acceptInt(int v) {
	  @ 	return true;
	  @ }
	  @*/

	/*@ model_behaviour
	  @ requires true;
	  @ static model boolean acceptBigInt(\bigint v) {
	  @ 	return true;
	  @ }
	  @*/

	//@ ghost boolean field = Test.acceptInt(1 + 2);

	/*@ model_behaviour
	  @ requires Test.acceptInt(1 + 2);
	  @ ensures Test.acceptInt(1 + 2);
	  @ static model boolean testModel() {
	  @ 	return Test.acceptInt(1 + 2);
	  @ }
	  @*/

	/*@ exceptional_behavior
	  @ signals (Exception) Test.acceptInt(1 + 2);
	  @*/
	/*@ normal_behaviour
	  @ requires Test.acceptInt(1 + 2);
	  @ ensures Test.acceptInt(1 + 2);
	  @ diverges Test.acceptInt(1 + 2);
	  @ measured_by Test.acceptInt(1 + 2);
	  @ determines field \by Test.acceptInt(1 + 2);
	  @*/
	public void test() {
		//@ ghost boolean t = Test.acceptInt(1 + 2);
		//@ set t = Test.acceptInt(1 + 2);
		//@ assert Test.acceptInt(1 + 2);
		/*@ normal_behaviour
	      @ requires Test.acceptInt(1 + 2);
	      @ ensures Test.acceptInt(1 + 2);
	      @ diverges Test.acceptInt(1 + 2);
	      @ breaks () Test.acceptInt(1 + 2);
	      @ continues () Test.acceptInt(1 + 2);
	      @ determines field \by Test.acceptInt(1 + 2);
	      @*/
		{;;}

		/*@ exceptional_behavior
	      @ returns Test.acceptInt(1 + 2);
	      @*/
		{;;}

		/*@ loop_invariant Test.acceptInt(1 + 2);
	      @ decreases Test.acceptInt(1 + 2);
	      @ determines field \by Test.acceptInt(1 + 2);
	      @*/
		for (int i = 0; i < 10; i++) {}
	}
}