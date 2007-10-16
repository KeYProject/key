package javax.realtime;

public class ScopedMemory extends MemoryArea{

    private Object portal;

    public static ScopedMemory currentMemoryArea;

    //@ public static invariant counter>=1;
    private static long counter=1;

    //@ public invariant (\forall ScopedMemory m; m!=null && m.id==id; m==this);
    private long id = counter++;

    /*@ public invariant referenceCount>=0 && (referenceCount>0 <==>
      @      stack!=null);
      @*/
    private int referenceCount=0;

    //@ public invariant stack!=null ==> (stack.top()==this && stack.stack.length>0);
    public MemoryStack stack;

    /*@ public invariant (\forall ScopedMemory m; (outerScope(m, this) <==>
      @      (stack!=null && (\exists int i; i>=0 && i<stack.stack.length; 
      @                       stack.stack[i]==m))));
      @*/

    /*@ public invariant (\forall MemoryStack ms; (\exists int i; i>=0 && i<ms.stack.length;
      @                                            ms.stack[i] == this) <==>
      @                                           ms.stack[stack.stack.length-1]==this);
      @*/

    public MemoryStack stack(){
	return stack;
    }

    public ScopedMemory parent=null;

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
	if(parent!=null && parent!=<currentMemoryArea>){
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
	if(parent!=null && parent!=<currentMemoryArea>){
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
	if(!<currentMemoryArea>.stack.contains(this)){
	    throw new InaccessableAreaException();
	}
	super.executeInArea(logic);
    }

    public long	getMaximumSize(){
	return size();
    }

    public java.lang.Object getPortal(){
	return portal;
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
	portal = object;
    }

    public java.lang.String toString(){
	return "ScopedMemory#"+id;
    }

}
