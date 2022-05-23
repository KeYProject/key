
public class ArrayAssignment {
		 
	/*@ public normal_behavior
	  @ requires \dl_noR(\dl_arrayRange(array,0,array.length-1)) && \dl_noW(\dl_arrayRange(array,0,array.length-1));
	  @ ensures \dl_noWaR(\dl_arrayRange(array,0,array.length-1));
	  @*/
	public static void arrayAssignment(int[] array) {
        int i = 0;
        /*@ loop_invariant 
          @ i>=0 && i<=array.length &&
          @ \dl_noWaR(\dl_arrayRange(array,0,array.length-1));
     	  @ assignable array[0..array.length-1];	
     	  @ decreases array.length - i;
          @*/
		while(i<=array.length-1){
			array[i]=1;
			i++;
		} 
	}

}
