
public class ArrayShift {
	 
	/*@ public normal_behavior
	  @ requires array.length > 0;
	  @ requires \dl_noR(\dl_arrayRange(array,0,array.length-1)) && \dl_noW(\dl_arrayRange(array,0,array.length-1));
	  @ ensures \dl_noRaW(\dl_arrayRange(array,0,array.length-1));
	  @*/
	public static void shift(int[] array) {
        int i = 0;
        /*@ loop_invariant 
          @  i>=0 && i<=array.length-1 &&
          @  \dl_noW(\dl_arrayRange(array,i,array.length-1)) && \dl_noR(\dl_arrayRange(array,i+1,array.length-1)) 
          @  && (i > 0 ==> \dl_noRaW(\dl_arrayRange(array,0,i-1)));
     	  @ assignable array[0..array.length-1];	
     	  @ decreases array.length - i;
          @*/
		while(i<array.length-1){
			array[i]=array[i+1];
			i++;
		} 
	}
	
}
