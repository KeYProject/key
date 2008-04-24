package javax.realtime;

public abstract class ScopedMemory extends MemoryArea{

    private Object portal;

    public static ScopedMemory currentMemoryArea;

    //@ public static invariant counter>=1;
    private static long counter=1;

    //@ public invariant (\forall ScopedMemory m; m!=null && m.id==id; m==this);
    private long id = counter++;

    /*@ public invariant referenceCount>=0 && (referenceCount>0 <==>
      @      stack!=null) && (referenceCount>0 <==> parent!=null);
      @*/
    private int referenceCount=0;

    //@ public invariant stack!=null ==> (stack.top()==this && stack._stack.length>0);
    public MemoryStack /*@nullable@*/ stack;

    /*@ public invariant (\forall ScopedMemory m; (\outerScope(m, this) <==>
      @      (stack!=null && (\exists int i; i>=0 && i<stack._stack.length; 
      @                       stack._stack[i]==m))));
      @*/

    /*@ public invariant (\forall MemoryStack ms; (\exists int i; i>=0 && i<ms._stack.length;
      @                                            ms._stack[i] == this) <==>
      @                                           ms._stack[stack._stack.length-1]==this);
      @*/

    public MemoryStack stack(){
	return stack;
    }

    //@ public invariant parent!=null ==> \outerScope(parent, this);
    public /*@nullable@*/ ScopedMemory parent=null;

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

    public void	enter(){
	/*	if(<currentMemoryArea>.stack.contains(this) || stack!=null &&
	   !<currentMemoryArea>.stack.push(this).equals(stack)){
	    throw new ScopedCycleException();
	    }*/
	if(stack!=null && outerScopeM(this, <currentMemoryArea>) ||
	   parent!=null && parent!=<currentMemoryArea>){
	    throw new ScopedCycleException();
	}
	parent = <currentMemoryArea>;
	stack = <currentMemoryArea>.stack.push(this);
	referenceCount++;
	try{
	    super.enter();
	}catch(Exception e){
	    if(this==e.memoryArea){
		throw new ThrowBoundaryError();
	    }
	}finally{
	    referenceCount--;
	    if(referenceCount==0){
		consumed=0;
		parent=null;
		stack=null;
	    }
	}
    }

    public void	enter(java.lang.Runnable logic){
	/*	if(<currentMemoryArea>.stack.contains(this) || stack!=null &&
	   !<currentMemoryArea>.stack.push(this).equals(stack)){
	    throw new ScopedCycleException();
	    }*/
	if(stack!=null && outerScopeM(this, <currentMemoryArea>) ||
	   parent!=null && parent!=<currentMemoryArea>){
	    throw new ScopedCycleException();
	}
	parent = <currentMemoryArea>;
	stack = <currentMemoryArea>.stack.push(this);
	referenceCount++;
	try{
	    super.enter(logic);
	}catch(Exception e){
	    if(this==e.memoryArea){
		throw new ThrowBoundaryError();
	    }
	}finally{
	    referenceCount--;
	    if(referenceCount==0){
		consumed=0;
		parent=null;
		stack=null;
	    }
	}
    }

    public void	executeInArea(java.lang.Runnable logic){
	//	if(!<currentMemoryArea>.stack.contains(this)){
	if(!outerScopeM(this, <currentMemoryArea>)){
	    throw new InaccessableAreaException();
	}
	super.executeInArea(logic);
    }

    /*@ public normal_behavior
      @  working_space 0;
      @  ensures \result==\outerScope(a,b);
      @*/
    public static /*@pure@*/ boolean outerScopeM(MemoryArea a, MemoryArea b);

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
	if(this==object.memoryArea){
	    portal = object;
	}else{
	    throw new IllegalAssignmentError();
	}
    }

    public java.lang.String toString(){
	return "ScopedMemory#"+id;
    }

}
