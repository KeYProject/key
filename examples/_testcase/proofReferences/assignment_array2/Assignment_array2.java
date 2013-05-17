package assignment_array2;

public class Assignment_array2 {
	 int val;
	 int[] as;
	 int index;
	 
	/*@ requires as != null;
	  @ requires index == 0;
	  @ requires as.length == 1;
	  @ ensures val == as[index];
	  @*/
	public void caller() {
		val = as[index];
	}
}
