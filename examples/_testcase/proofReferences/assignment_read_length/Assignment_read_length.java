package assignment_read_length;

public class Assignment_read_length {
   boolean[] b;
   
	/*@ requires true;
	  @ ensures true;
	  @*/
	public void caller() {
		int a;
		a = b.length;
	}
}
