public class YLoop {
	int _PB_NY, _PB_NX;
	int[][] A = new int [_PB_NX][_PB_NY];
	int[] tmp = new int [_PB_NX];
	int[] y = new int [_PB_NY];
	
	/*@ public normal_behavior
	  @ requires i >= 0 && i < _PB_NX;
	  @ requires _PB_NX > 0 && _PB_NY > 0 && A.length == _PB_NX &&
	  @ (\forall int i; i >= 0 && i < _PB_NX; A[i].length == _PB_NY) &&
	  @ tmp.length == _PB_NX && y.length == _PB_NY;
	  @	requires (\forall int i; i >= 0 && i < _PB_NX; A[i] != y && A[i] != tmp);
	  @ requires tmp != y;
	  @ requires \dl_noRaW(\dl_arrayRange(tmp, 0, _PB_NX-1)) &&
	  @ 		 \dl_noW(\dl_arrayRange(tmp, 0, _PB_NX-1)) &&
	  @ 		 \dl_noR(\dl_arrayRange(tmp, 0, _PB_NX-1));
	  @ ensures \dl_noRaW(\dl_arrayRange(tmp, 0, _PB_NX-1));
	  @*/
	public void yLoop(int i) {			
		  /*@ loop_invariant 
	        @ j >= 0 && j <= _PB_NY &&
	        @ \dl_noRaW(\dl_arrayRange(tmp, 0, _PB_NX-1)) &&
            @ \dl_noW(\dl_arrayRange(tmp, 0, _PB_NX-1));
	   	  	@ assignable y[0.._PB_NY-1];	
	   	  	@ decreases _PB_NY-j;
	        @*/
	      for (int j = 0; j < _PB_NY; j++)
	    	  y[j] = y[j] + A[i][j] * tmp[i];
			
	    }
	}
