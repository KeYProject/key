public class Atax {

	int _PB_NY, _PB_NX;
	int[][] A = new int [_PB_NX][_PB_NY];
	int[] tmp = new int [_PB_NX];
	int[] x = new int [_PB_NY];
	int[] y = new int [_PB_NY];
	
	/*@ public normal_behavior
	  @ requires _PB_NX>0 && _PB_NY>0 && A.length==_PB_NX &&
	  @ (\forall int i; i>=0 && i<_PB_NX; A[i].length==_PB_NY) &&
	  @ tmp.length==_PB_NX && x.length==_PB_NY && y.length==_PB_NY;
	  @ requires (\forall int i; i>=0 && i<_PB_NX; (\forall int j; j>=0 && j<_PB_NX && i!=j; A[i]!=A[j]));
	  @	requires (\forall int i; i>=0 && i<_PB_NX; A[i] != tmp && A[i] != x && A[i] != y);
	  @ requires ( tmp!=x && tmp!=y && x!=y);
	  @ requires \dl_noR(\infinite_union(int i; i>=0 && i<_PB_NX; \dl_arrayRange(A[i],0,_PB_NY-1))) &&
	  @          \dl_noW(\infinite_union(int i; i>=0 && i<_PB_NX; \dl_arrayRange(A[i],0,_PB_NY-1))) &&
	  @          \dl_noRaW(\infinite_union(int i; i>=0 && i<_PB_NX; \dl_arrayRange(A[i],0,_PB_NY-1)));
	  @ ensures \dl_noRaW(\infinite_union(int i; i>=0 && i<_PB_NX; \dl_arrayRange(A[i],0,_PB_NY-1)));
	  @*/
	public void atax() {
		int i =0;
		int j = 0;
		
		/*@ loop_invariant 
		@ i>=0 && i <= _PB_NY &&
        @ \dl_noRaW(\infinite_union(int k; k>=0 && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1))) &&
        @ \dl_noW(\infinite_union(int k; k>=0 && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1))) &&
        @ \dl_noR(\infinite_union(int k; k>=0 && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1)));
 	    @ assignable  y[0.._PB_NY-1];	
 	  	@ decreases _PB_NY-i;
        @*/		
		for (i = 0; i < _PB_NY; i++) {
		  y[i] = 0;
		}
		
		
		
		/*@ loop_invariant 
		  @ i>=0 && i <= _PB_NX &&
          @ \dl_noRaW(\infinite_union(int k; k>=0 && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1))) &&
          @ \dl_noW(\infinite_union(int k; k>=0 && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1))); 
         // @ \dl_noR(\infinite_union(int k; k>=i && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1)));		   	  	
   	  	  @ assignable tmp[0.._PB_NX-1], y[0.._PB_NY-1];	
   	  	  @ decreases _PB_NX-i;
          @*/
		for (i = 0; i < _PB_NX; i++)
		    {
		      tmp[i] = 0;
		      /*@ loop_invariant 
		        @ j>=0 && j <= _PB_NY &&
				@ \dl_noRaW(\infinite_union(int k; k>=0 && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1))) &&
                @ \dl_noW(\infinite_union(int k; k>=0 && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1)));
                @//  \dl_noR(\infinite_union(int k; k>=i && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1)));		   	  	
                @ assignable tmp[i];	
		   	  	@ decreases _PB_NY-j;
		        @*/
		      for (j = 0; j < _PB_NY; j++)
		    	  tmp[i] = tmp[i] + A[i][j] * x[j];
		      /*@ loop_invariant 
		        @ j>=0 && j <= _PB_NY &&
		        @ \dl_noRaW(\infinite_union(int k; k>=0 && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1))) &&
                @ \dl_noW(\infinite_union(int k; k>=0 && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1)));
                @ //\dl_noR(\infinite_union(int k; k>i && k<_PB_NX; \dl_arrayRange(A[k],0,_PB_NY-1)));
		   	  	@ assignable y[0.._PB_NY-1];	
		   	  	@ decreases _PB_NY-j;
		        @*/
		      for (j = 0; j < _PB_NY; j++)
		    	  y[j] = y[j] + A[i][j] * tmp[i];
		    }
		}
}
