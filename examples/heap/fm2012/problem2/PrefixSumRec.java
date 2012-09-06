//import java.util.Arrays;

class PrefixSumRec {

    private int[] a;

    PrefixSumRec(int [] a) {
	this.a = a;
    }


    public void upsweep(int left, int right) {
        if (right > left+1) {
            int space = right - left;
            upsweep(left-space/2,left);
            upsweep(right-space/2,right);
        }
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
