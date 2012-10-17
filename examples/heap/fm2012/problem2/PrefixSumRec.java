// import java.util.Arrays;

class PrefixSumRec {

    private final int[] a; // non_null

    PrefixSumRec(int [] a) {
	this.a = a;
    }


    /*@ public normal_behavior
      @  requires x > 0;
      @  ensures \result ==> (x % 2 == 0  && isPow2(x/2) || x == 1);
      @  measured_by x;
      @  strictly_pure
      @*/
    private boolean isPow2(int x){
      if (x==1) 
          return true;
      else if (x % 2 != 0 ) 
          return false;
      else 
          return isPow2(x/2);
    } // proof requires induction (hypothesis: isPow(pow(2,n)))

    /*@ public normal_behavior
          requires right > left;
          requires left >= 0;
          requires right < a.length;
          requires isPow2(a.length);
          requires isPow2(right - left);
          // requires right % 2 == 0 && (left % 2 == 0 || right - left == 1);
          //ensures a[right] == (\sum int i; 0 <= i && i < right; \old(a[i]));
          ensures a[right] == (\sum int i; 2*left-right+1 <= i && i < right+1; \old(a[i]));
          measured_by right - left;
          assignable a[*]; // every second entry <= right
      @*/
    public void upsweep(int left, int right) {
        int space = right - left;
        if (space > 1) {
            upsweep(left-space/2,left);
            upsweep(right-space/2,right);
        }
        // @ assert space == 1;
        a[right] = a[left]+a[right];
    }
    

    public void downsweep(int left, int right) {
        int tmp = a[right];
        a[right] = a[right] + a[left];
        a[left] = tmp;
        if (right > left+1) {
            int space = right - left;
            downsweep(left-space/2,left);
            downsweep(right-space/2,right);
        }
    
    }

/*       
    public static void main (String [] args) {
        int [] a = {3,1,7,0,4,1,6,3};
        PrefixSumRec p = new PrefixSumRec(a);
        System.out.println(Arrays.toString(a));
        p.upsweep(3,7);
        System.out.println(Arrays.toString(a));
        a[7]=0;
        p.downsweep(3,7);
        System.out.println(Arrays.toString(a));
    }
*/
}


/*
[3, 1, 7, 0, 4, 1, 6, 3]
[3, 4, 7, 11, 4, 5, 6, 25]
[0, 3, 4, 11, 11, 15, 16, 22]



*/
