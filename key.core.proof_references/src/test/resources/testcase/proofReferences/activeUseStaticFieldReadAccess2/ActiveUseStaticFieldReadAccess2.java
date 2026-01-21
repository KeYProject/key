package activeUseStaticFieldReadAccess2;

public class ActiveUseStaticFieldReadAccess2 {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public void caller(Class callme) {
		int i;
		i = callme.i + 2;
	}
}
