import javax.realtime.*;

public abstract class B{

    /*@ public normal_behavior
      @  requires x>=0 && y>=0 && \outerScope(this.memoryArea, \currentMemoryArea);
      @  working_space \space(LTMemory)+\space(PhysicalMemoryArea)+\space(Runnable)+8;
      @*/
    public final void foo(final int x, final int y){
	ScopedMemory m = new LTMemory(24*x+16);
	Runnable r = new Runnable(){
		public void run(){
		    int j=0;
		    final A[] a = new A[x];
		    /*@ loop_invariant j>=0 && (\forall int k; k>=0 && k<j; a[k]!=null);
		      @ assignable j, a[*];
		      @ decreasing x-j;
		      @ working_space_single_iteration \space(A);
		      @*/
		    while(j<x){
			a[j] = new A();
			j++;
		    }
		    bar(a);
		}
	    };
	int i=0;
	/*@ loop_invariant i>=0;
	  @ assignable i;
	  @ decreasing y-i;
	  @ working_space_single_iteration 0;
	  @*/
	while(i<y){
	    m.enter(r);
	    i++;
	}
    }

    /*@ public normal_behavior
      @  assignable a[*], a[*].c;
      @  working_space 0;
      @*/
    public void bar(A[] a);

}
