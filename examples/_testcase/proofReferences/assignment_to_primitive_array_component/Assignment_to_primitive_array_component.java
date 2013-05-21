package assignment_to_primitive_array_component;

public class Assignment_to_primitive_array_component {
	int index;
	boolean[] bs;
	
	/*@ requires bs.length == 1;
	  @ requires index == 0;
	  @ ensures true;
	  @*/
	public void caller() {
		bs[index] = false;
	}
}
