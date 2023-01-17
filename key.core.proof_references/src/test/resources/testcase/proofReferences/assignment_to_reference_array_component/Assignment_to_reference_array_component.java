package assignment_to_reference_array_component;

public class Assignment_to_reference_array_component {
   String[] bs;
   
	/*@ requires \typeof(bs) == \type(String[]) && bs.length == 1;
	  @ ensures true;
	  @*/
	public void caller(String o) {
		bs[0] = o;
	}
}
