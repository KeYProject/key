package tests;

/**
 * The Class Caller.
 */
public class Caller {
	
    private/* @ spec_public @ */int i;
	
	public  Caller(){
		i=0;		
	}
	
	/**
	 * Calling function.
	 * 
	 * This function may cause a class cast exception
	 * 						  or nullpointer exception
	 * @param o the object
	 * 
	 * @return the int
	 */

		/*@ public normal_behavior
		 ensures true; @*/
	
	public int callingFunction(Object o) {

		// if(o!=null)
	//		 i++;
		i = ((ClassA2)o).myFunction();
		return i;
	}
}