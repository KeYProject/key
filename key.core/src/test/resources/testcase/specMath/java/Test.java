// This test uses method resolution to return BigIntMarker or IntMarker from the accept model method
// Test failure is indicated by method resolution failing
public /*@ spec_java_math @*/ class Test {
	public static class BigIntMarker {
		public boolean isBigint() {
			return true;
		}
	}

	public static class IntMarker {
		public boolean isInt() {
			return true;
		}
	}

	/*@ model_behaviour
	  @ requires true;
	  @ static model IntMarker accept(int v);
	  @*/

	public int spacer5;

	/*@ model_behaviour
	  @ requires true;
	  @ static model BigIntMarker accept(\bigint v);
	  @*/

	public int spacer4;

	//@ ghost boolean field = Test.accept(1 + 2).isInt();

	public int spacer3;

	/*@ model_behaviour
	  @ requires Test.accept(1 + 2).isInt();
	  @ ensures Test.accept(1 + 2).isInt();
	  @ accessible t[Test.accept(1 + 2).isInt() ? 1 : 0..t.length];
	  @ static model boolean testModel(int[] t) {
	  @ 	return Test.accept(1 + 2).isInt();
	  @ }
	  @*/

	public int spacer2;

	/*@ model_behaviour
	  @ requires Test.accept(1 + 2).isBigint();
	  @ ensures Test.accept(1 + 2).isBigint();
	  @ accessible t[Test.accept(1 + 2).isBigint() ? 1 : 0..t.length];
	  @ static spec_bigint_math model boolean testBigModel(int[] t) {
	  @ 	return Test.accept(1 + 2).isBigint();
	  @ }
	  @*/

	// Model methods math mode infects methods
	public int spacer;

	/*@ exceptional_behavior
	  @ signals (Exception) Test.accept(1 + 2).isBigint();
	  @*/
	/*@ normal_behaviour
	  @ requires Test.accept(1 + 2).isBigint();
	  @ ensures Test.accept(1 + 2).isBigint();
	  @ diverges Test.accept(1 + 2).isBigint();
	  @ measured_by Test.accept(1 + 2).isBigint();
	  @ determines field \by Test.accept(1 + 2).isBigint();
	  @*/
	public /*@ spec_bigint_math @*/void test() {
		// ghost boolean t = Test.accept(1 + 2).isBigint() && \java_math(Test.accept(1 + 2).isInt());
		// set t = Test.accept(1 + 2).isBigint();
		//@ assert Test.accept(1 + 2).isBigint();
		/*@ normal_behaviour
	      @ requires Test.accept(1 + 2).isBigint();
	      @ ensures Test.accept(1 + 2).isBigint();
	      @ diverges Test.accept(1 + 2).isBigint();
	      @ breaks () Test.accept(1 + 2).isBigint();
	      @ continues () Test.accept(1 + 2).isBigint();
	      @ determines field \by Test.accept(1 + 2).isBigint();
	      @*/
		{;;}

		/*@ exceptional_behavior
	      @ returns Test.accept(1 + 2).isBigint();
	      @*/
		{;;}

		/*@ loop_invariant Test.accept(1 + 2).isBigint();
	      @ decreases Test.accept(1 + 2).isBigint();
	      @ determines field \by Test.accept(1 + 2).isBigint();
	      @*/
		for (int i = 0; i < 10; i++) {}
	}

	/*@ exceptional_behavior
	  @ signals (Exception) Test.accept(1 + 2).isInt();
	  @*/
	/*@ normal_behaviour
	  @ requires Test.accept(1 + 2).isInt();
	  @ ensures Test.accept(1 + 2).isInt();
	  @ diverges Test.accept(1 + 2).isInt();
	  @ measured_by Test.accept(1 + 2).isInt();
	  @ determines field \by Test.accept(1 + 2).isInt();
	  @*/
	public void testJavaMath() {
		// ghost boolean t = Test.accept(1 + 2).isInt() && \bigint_math(Test.accept(1 + 2).isBigint());
		// set t = Test.accept(1 + 2).isInt();
		//@ assert Test.accept(1 + 2).isInt();
		/*@ normal_behaviour
	      @ requires Test.accept(1 + 2).isInt();
	      @ ensures Test.accept(1 + 2).isInt();
	      @ diverges Test.accept(1 + 2).isInt();
	      @ breaks () Test.accept(1 + 2).isInt();
	      @ continues () Test.accept(1 + 2).isInt();
	      @ determines field \by Test.accept(1 + 2).isInt();
	      @*/
		{;;}

		/*@ exceptional_behavior
	      @ returns Test.accept(1 + 2).isInt();
	      @*/
		{;;}

		/*@ loop_invariant Test.accept(1 + 2).isInt();
	      @ decreases Test.accept(1 + 2).isInt();
	      @ determines field \by Test.accept(1 + 2).isInt();
	      @*/
		for (int i = 0; i < 10; i++) {}
	}
}