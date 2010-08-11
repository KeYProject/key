import javax.realtime.*;

public class MatrixProduct{

    /*@ public normal_behavior
      @  requires (\forall int i,j; 0<=i && i<matrices.length && 
      @     0<=j && j<matrices[i].length; 
      @     \nonnullelements(matrices[i]) &&
      @     matrices[i].length == factor.length && factor.length == result.length &&
      @     matrices[i][j].length == factor[j].length && factor[j].length == result[j].length &&
      @     factor.length == factor[j].length) && \nonnullelements(matrices) &&
      @     \nonnullelements(factor) && \nonnullelements(result); 
      @*/
    public boolean match(final int[][][] matrices, int[][] factor, int[][] result){
	Runnable produce = new Runnable(){
		public boolean found=false; 

		
	    };
	return false;
    }

    /*@ public normal_behavior
      @  requires \nonnullelements(m1) && \nonnullelements(m2);
      @  working_space 0;
      @  ensures \result <==> ((\forall int i,j; 0<=i && i<m1.length && 
      @     0<=j && j<m1[i].length; m1[i].length == m2[i].length && m1[i][j]==m2[i][j]) && 
      @     m1.length==m2.length);
      @*/
    public /*@pure@*/ boolean equal(int[][] m1, int[][] m2){
	if(m1.length!=m2.length) return false;
	/*@ loop_invariant (\forall int k,l; k>=0 && k<i && l>=0 && l<=m1[i].length; 
	  @    m1[k].length==m2[k].length && m1[k][l]==m2[k][l]);
	  @ assignable i;
	  @ decreasing m1.length-i;
	  @ working_space_single_iteration 0;
	  @*/
	for(int i=0; i<m1.length; i++){
	    if(m1[i].length!=m2[i].length) return false;
	    /*@ loop_invariant (\forall int k,l; k>=0 && k<i && l>=0 && l<=j; 
	      @    m1[k][l]==m2[k][l]);
	      @ assignable j;
	      @ decreasing m1[i].length-j;
	      @ working_space_single_iteration 0;
	      @*/
	for(int j=0; j<m1[i].length; j++){
		if(m1[i][j]!=m2[i][j]) return false;
	    }
	}
	return true;
    }

}


