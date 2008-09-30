import javax.realtime.*;

public abstract class BBug{

    /*@ public normal_behavior
      @  requires x>=0 && y>=0;
      @  working_space \space(LTMemory)+\space(Runnable);
      @*/
    public static final void /*@scopeSafe@*/ foo(final int x, final int y){
	ScopedMemory m = new LTMemory(24*x+16);
	Runnable r = new Runnable(){
		public void run(){
		    int j=0;
		    A[] a = new A[x];
		    /*@ loop_invariant j>=0 && (\forall int k; k>=0 && k<j; a[k]!=null) && \object_creation(A);
		      @ assignable j, a[*], \object_creation(A);
		      @ decreasing x-j;
		      @ working_space_single_iteration \space(A);
		      @*/
		    while(j<x){
			a[j] = new A();
			j++;
		    }
		    BBug.bar(a);
		}
	    };
	int i=0;
	/*@ loop_invariant i>=0 && \object_creation(A) && \object_creation(A[]) && \object_creation(MemoryStack);
	  @ assignable i, \object_creation(A), \object_creation(A[]), \object_creation(MemoryStack);
	  @ decreasing y>0 ? y-i : 0;
	  @ working_space_single_iteration 0;
	  @*/
	while(i<y){
	    m.enter(r);
	    i++;
	}
    }

    /*@ public normal_behavior
      @  assignable \nothing; 
      @  working_space 0;
      @*/
    public static void bar(A[] a);

}
