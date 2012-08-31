//import java.util.Arrays;

class PrefixSumIter {

    private int[] a;


    PrefixSumIter(int [] a) {
	this.a = a;
    }


    public int upsweep() {
        int space = 1;
        for (; space < a.length; space=space*2) {
            int left = space - 1;
            while (left < a.length) {
                int right = left + space;
                a[right] = a[left] + a[right];
                left = left + space*2;
            }
        }
        return space;
    }
    

    public void downsweep(int space) {
        a[a.length - 1] = 0;
        space = space/2;
        for (; space > 0; space=space/2) {
            int right = space*2 - 1;
            while (right < a.length) {
                int left = right - space;
                int temp = a[right];
                a[right] = a[left] + a[right];
                a[left] = temp;
                right = right + space*2;
            }
        }
    }
 
/*
    public static void main (String [] args) {
        int [] a = {3,1,7,0,4,1,6,3};
        PrefixSumIter p = new PrefixSumIter(a);
        System.out.println(Arrays.toString(a));
        int space = p.upsweep();
        System.out.println(space);        
        System.out.println(Arrays.toString(a));
        p.downsweep(space);
        System.out.println(Arrays.toString(a));
    }
*/

}


/*
[3, 1, 7, 0, 4, 1, 6, 3]
[3, 4, 7, 11, 4, 5, 6, 25]
[0, 3, 4, 11, 11, 15, 16, 22]



*/
