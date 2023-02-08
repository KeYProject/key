package assignment_write_static_attribute;

public class Assignment_write_static_attribute {
   static boolean b;
   
	/*@ requires true;
	  @ ensures true;
	  @*/
	public void caller() {
		b = false;
	}
}
