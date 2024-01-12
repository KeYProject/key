package activeUseStaticFieldWriteAccess2;

public class ActiveUseStaticFieldWriteAccess2 {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public void caller(Class callme) {
		callme.a = false;
	}
}
