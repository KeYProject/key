package javax.realtime;

public abstract class ScopedMemory extends MemoryArea{

    private /*@nullable@*/ Object portal;

    // public static invariant counter>=1;
    //    private static long counter=1;

    // public invariant (\forall ScopedMemory m; m!=null && m.id==id; m==this);
    //    private long id = counter++;


    /* public invariant (\forall ScopedMemory m; (\outerScope(m, this) <==>
      @      (stack!=null && (\exists int i; i>=0 && i<stack._stack.length; 
      @                       stack._stack[i]==m))));
      @*/

    /* public invariant (\forall ScopedMemory s; (\exists int i; i>=0 && i<s.stack._stack.length;
      @                                            s.stack._stack[i] == this) <==>
      @                                           s.stack._stack[stack._stack.length-1]==this);
      @*/

    public ScopedMemory(long size){
	super(size);
    }

    public ScopedMemory(long size, java.lang.Runnable logic){
	super(size, logic);
    }

    public ScopedMemory(SizeEstimator size){
	super(size);
    }

    public ScopedMemory(SizeEstimator size, java.lang.Runnable logic){
	super(size, logic);
    }

    public long	getMaximumSize(){
	return size();
    }

    public java.lang.Object getPortal(){
	if(outerScopeM(this, <currentMemoryArea>)){
	    return portal;
	}else{
	    throw new IllegalAssignmentError();
	}
    }

    //    public int getReferenceCount(){ }

    //    public void join(){}

    //    public void join(HighResolutionTime time){}

    public void	joinAndEnter(){}

    //    public void joinAndEnter(HighResolutionTime time){}

    //    public void joinAndEnter(java.lang.Runnable logic){}

    //public void joinAndEnter(java.lang.Runnable logic, HighResolutionTime time)
    java.lang.Object newArray(java.lang.Class type, int number){
	super.newArray(type, number);
    }

    //    public java.lang.Object newInstance(java.lang.Class type){}

    //    public java.lang.Object newInstance(java.lang.reflect.Constructor c, 
    //	java.lang.Object[] args){}

    public void setPortal(java.lang.Object object){
	if(this==getMemoryArea(object)){
	    portal = object;
	}else{
	    throw new IllegalAssignmentError();
	}
    }

    /*    public java.lang.String toString(){
	return "ScopedMemory#"+id;
	}*/

}
