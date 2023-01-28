package assignment_write_attribute;

public class Assignment_write_attribute {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public void caller(Class callme){
		callme.a = false;
	}
}
