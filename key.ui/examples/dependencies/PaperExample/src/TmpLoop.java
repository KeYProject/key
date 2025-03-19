//
//public class TmpLoop {
//	int _PB_NY, _PB_NX;
//	int[][] A = new int [_PB_NX][_PB_NY];
//	int[] tmp = new int [_PB_NX];
//	int[] x = new int [_PB_NY];
//	
//	/*@ public normal_behavior
//	  @ requires _PB_NX>0 && _PB_NY>0 && A.length==_PB_NX &&
//	  @ (\forall int i; i>=0 && i<_PB_NX; A[i].length==_PB_NY) &&
//	  @ tmp.length==_PB_NX && x.length==_PB_NY;
//	  @	requires (\forall int i; i>=0 && i<_PB_NX; A[i] != tmp);
//	  @ requires (tmp!=x);
//	  @ requires ;
//	  @ ensures true;
//	  @*/
//	public void tmpLoop() {
//	/*@ loop_invariant 
//	  @ i>=0 && i <= _PB_NX && 
//	  @ \dl_noW(\dl_arrayRange(tmp,i+1,_PB_NX-1)) &&
//	  @ \dl_noR(\dl_arrayRange(tmp,i+1,_PB_NX-1)) &&
//	  @ \dl_noRaW(\dl_arrayRange(tmp,i+1,_PB_NX-1));		   	  	
//  	  @ assignable tmp[0.._PB_NX-1];	
//  	  @ decreases _PB_NX-i;
//      @*/
//		for(int i =0; i< _PB_NX; i++)
//		/*@ loop_invariant 
//		  @ j>=0 && j <= _PB_NY;		   	  	
// 	  	  @ assignable tmp[i];	
// 	  	  @ decreases _PB_NY-j;
//          @*/
//			for (int j = 0; j < _PB_NY; j++) {
//		      tmp[i] = tmp[i] + A[i][j] * x[j];
//		      
//		    	  
//			}
//		
//	}
//}
