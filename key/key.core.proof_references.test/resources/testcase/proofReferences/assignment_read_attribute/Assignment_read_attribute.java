package assignment_read_attribute;

public class Assignment_read_attribute {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public void caller(Class callme) {
		callme.a = callme.b + callme.b;
	}
}
