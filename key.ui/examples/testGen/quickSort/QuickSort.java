public class QuickSort{

    /*@ public normal_behavior
      @  requires a!=null && a.length<4;
      @  requires lo<hi && 0<=lo && hi<a.length;
      @  ensures a!=null ==> (\forall int i; lo<=i && i<hi; 
      @                        a[i]<=a[i+1]) &&
      @                      (\forall int i;lo<=i && i<=hi; 
      @                        (\exists int j; lo<=j && j<=hi; 
      @                          \old(a[i]) == a[j]));
      @*/
    public static void sort(int[] a, int lo, int hi){
	int i=lo, j=hi, h;
	int x=a[lo];

	//  partition
	do{    
	    while (a[i]<x) i++; 
	    while (a[j]>x) j--;
	    if (i<=j)
	    {
		h=a[i]; a[i]=a[j]; a[j]=h;
		i++; j--;
	    }
	} while (i<=j);

	//  recursion
	if (lo<j) sort(a, lo, j);
	if (i<hi) sort(a, i, hi);
    }

}
