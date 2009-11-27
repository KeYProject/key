//example from "Concurrent and Real-Time Programming in Java" by Andy Wellings
import javax.realtime.*;

public class MatrixExample{

    public static final int[][] unity = {{1,0},{0,1}};

    public int[][][] table;

    /*@ public invariant (\forall int i; 0<=i && i<table.length; 
      @       table[i]!=null && table[i].length==2 &&
      @       table[i][0]!=null && table[i][1]!=null &&
      @       table[i][0].length==2 && table[i][1].length==2);
      @*/

    /*@ public normal_behavior
      @  requires a!=null && b!=null && a.length==2 && b.length==2 &&
      @     a[0]!=null && a[0].length==2 && a[1]!=null && a[1].length==2 &&
      @     b[0]!=null && b[0].length==2 && b[1]!=null && b[1].length==2;
      @  assignable \object_creation(int[][]);
      @  working_space \space(int[2][2]);
      @*/
    private int[][] /*@scopeSafe@*/ dotProduct(int[][] a, int[][] b){
	int[][] result = new int[2][2];
	result[0][0] = a[0][0]*b[0][0]+a[0][1]*b[1][0];
	result[0][1] = a[0][0]*b[0][1]+a[0][1]*b[1][1];
	result[1][0] = a[1][0]*b[0][0]+a[1][1]*b[1][0];
	result[1][1] = a[1][0]*b[0][1]+a[1][1]*b[1][1];
	return result;
    }

    /*@ public normal_behavior
      @  requires a!=null && b!=null && a.length==2 && b.length==2 &&
      @     a[0]!=null && a[0].length==2 && a[1]!=null && a[1].length==2 &&
      @     b[0]!=null && b[0].length==2 && b[1]!=null && b[1].length==2;
      @  assignable \nothing;
      @  working_space 0;
      @  ensures \result <==> (a[0][0]==b[0][0] && a[1][1]==b[1][1] && a[0][1]==b[0][1] 
      @	    && a[1][0]==b[1][0]);
      @*/
    private boolean /*@scopeSafe@*/ /*@pure@*/ equals(int[][] a, int[][] b){
	return a[0][0]==b[0][0] && a[1][1]==b[1][1] && a[0][1]==b[0][1] 
	    && a[1][0]==b[1][0];
    }

    /*@ public normal_behavior
      @  requires a!=null && a.length==2 && 
      @     a[0]!=null && a[0].length==2 && a[1]!=null && a[1].length==2 &&
      @     \outerScope(\memoryArea(a), \currentMemoryArea) && \outerScope(\memoryArea(this), \currentMemoryArea);
      @  working_space \space(LTMemory) + \space(Product);
      @*/
    public int match(final int[][] a){
	Product produce = new Product();
	ScopedMemory myMem = new LTMemory(1000);
	int i=0;
	/*@ loop_invariant i>=0 && i<=table.length && \object_creation(int[][]);
	  @ assignable i, produce.j, produce.withMatrix, produce.found, \object_creation(int[][]);
	  @ decreasing table.length-i;
	  @ working_space_single_iteration 0;
	  @*/
	while(i<table.length){
	    produce.j = i++;
	    produce.withMatrix = a;
	    myMem.enter(produce);
	}
	return produce.found;
    }

    private class Product implements Runnable{
	int j;
	int[][] withMatrix;
	int found = 0;

	public void run(){
	    int[][] product = dotProduct(table[j], withMatrix);
	    if(MatrixExample.this.equals(product, unity)) found++;
	}
    }
}
