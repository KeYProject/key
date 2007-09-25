public class ReverseArray {

    public int[] a;     
   
    public int[] a0;

    public ReverseArray() {
    }
    
    
    /*@ public normal_behavior
      @ requires a!=null && a.length>=0 && a!=a0 && a0!=null &&
      @    a0.length == a.length && (\forall int h; h>=0 && h<a.length; a0[h]==a[h]);
      @ ensures (\forall int j; j>=0 && j<a.length; a[j]==\old(a[a.length-(j+1)]));
      @ diverges true;
      @*/
    public void reverse() {
	int i = 0;

        final int length = (a.length/2) ;
	/*@ 
	  @ loop_invariant
	  @   (\forall int j; j>=0 && j<i; a0[a.length-(j+1)]==a[j] && a0[j]==a[a.length-(j+1)])
	  @   && (\forall int j; j>=i && j<length; a0[a.length-(j+1)]==a[a.length-(j+1)] && a0[j]==a[j])
	  @   && (a.length % 2 != 0 ==> a0[length]==a[length])
	  @   && i>=0 && i<=length;
	  @ modifies a[*], i;
	  @*/	
	while (i<length) {
	    int tmp = a[i];
	    a[i] = a[a.length-(i+1)];
	    a[a.length-(i+1)] = tmp;
	    i++;
	}
    }



    /*@ public normal_behavior
      @ requires p_a!=null && p_a.length>=0;
      @ ensures (\forall int j; j>=0 && j<\old(p_a.length); \result[j]==\old(p_a[p_a.length-(j+1)])) &&
      @	\result.length == \old(p_a.length);
      @ diverges true;
      @*/
    public int[] reverse2(int[] p_a) {
        int[] b = new int[p_a.length];
	int i = 0;
	/*@ 
	  @ loop_invariant (\forall int j; j>=0 && j<i; b[j]==p_a[p_a.length-(j+1)]) && i>=0 && i<=p_a.length;
	  @ modifies b[*], i;
	  @*/
	while (i<p_a.length) {      
 	    b[i] = p_a[p_a.length-(i+1)];      
	    i++;
	}
	return b;
    }

   public static void main(String[] args) {
       ReverseArray ra = new ReverseArray();
       ra.a = new int[]{1,2,3,4,5,6,7,8,9};
       for (int i = 0; i<ra.a.length; i++) {
         System.out.println(ra.a[i]);
       }
       ra.reverse2(ra.a);
       for (int i = 0; i<ra.a.length; i++) {
         System.out.println(ra.a[i]);
       }
     
   }

}

