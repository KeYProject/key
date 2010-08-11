package javax.realtime;

public abstract class MemoryArea{

    public static MemoryArea currentMemoryArea;

    // PERC Pico specific
    //    public static MemoryArea callerScope;
    //    public static MemoryArea constructedScope;

    // public invariant stack!=null ==> (stack.top()==this && stack._stack.length>0);
    public MemoryStack /*@nullable@*/ stack;

    public MemoryStack stack(){
	return stack;
    }

    //@ public invariant parent==this <==> this==ImmortalMemory.instance;
    //@ public invariant parent==null <==> stack==null;
    //@ public invariant parent==null ==> consumed==0;
    public /*@nullable@*/ MemoryArea parent=null;

    /*@ public invariant referenceCount>=0 && (referenceCount>0 <==>
      @      stack!=null) && 
      @     (referenceCount>0 <==> parent!=null);
      @*/
    protected int referenceCount=0;

    protected final long size;
    protected long consumed;
    protected final /*@ nullable @*/ java.lang.Runnable logic;

    //    protected final PhysicalMemoryArea memory;

    protected MemoryArea(long size){
	this(size, null);
    }

    protected MemoryArea(long size, java.lang.Runnable logic){
	if(size<0) throw new java.lang.IllegalArgumentException();
	this.size = size;
	this.logic = logic;
	//	<currentMemoryArea>.consumed -= 8;
	//	memory = new PhysicalMemoryArea(size);
    }

    protected MemoryArea(SizeEstimator size){
	this(size, null);
    }

    protected MemoryArea(SizeEstimator size, java.lang.Runnable logic){
	if(size==null || size.getEstimate()<0){
	    throw new IllegalArgumentException();
	}
	this.size = size.getEstimate();
	this.logic = logic;
	//	memory = new PhysicalMemoryArea(this.size);
    }

    private void <runRunnable>(java.lang.Runnable logic){
	logic.run();
    }

    private void delete(MemoryArea m);

    public void	enter(){
	if(logic==null) throw new IllegalArgumentException();
	if(//stack!=null && outerScopeM(this, <currentMemoryArea>) ||
	   parent!=null && parent!=<currentMemoryArea>){
	    throw new ScopedCycleException();
	}
	parent = <currentMemoryArea>;
	if(stack==null){
	    stack = <currentMemoryArea>.stack.push(this);
	}
	referenceCount++;
	try{
	    <runRunnable>(logic);
	}catch(Exception e){
	    if(this==getMemoryArea(e)){
		throw RealtimeSystem.tbe();
	    }
	}finally{
	    referenceCount--;
	    if(referenceCount==0){
		delete(RealtimeSystem.TRASH);
		consumed=0;
		parent=null;
		stack=null;
	    }
	}
    }

    public void	enter(java.lang.Runnable logic){
	if(logic==null) throw new IllegalArgumentException();
	if(//stack!=null && outerScopeM(this, <currentMemoryArea>) ||
	   parent!=null && parent!=<currentMemoryArea>){
	    throw new ScopedCycleException();
	}
	parent = <currentMemoryArea>;
	if(stack==null){
	    stack = <currentMemoryArea>.stack.push(this);
	}
	referenceCount++;
	try{
	    <runRunnable>(logic);
	}catch(Exception e){
	    if(this==getMemoryArea(e)){
		throw RealtimeSystem.tbe();
	    }
	}finally{
	    referenceCount--;
	    if(referenceCount==0){
		delete(RealtimeSystem.TRASH);
		consumed=0;
		parent=null;
		stack=null;
	    }
	}
    }

    public void	executeInArea(java.lang.Runnable logic){
	if(logic==null) throw new IllegalArgumentException();
	if(!outerScopeM(this, <currentMemoryArea>)){
	    throw new InaccessibleAreaException();
	}
	<runRunnable>(logic);
    }

    /*@ public normal_behavior
      @  working_space 0;
      @  ensures \result==\outerScope(a,b);
      @*/
    public static /*@pure@*/ boolean outerScopeM(MemoryArea a, MemoryArea b);

    /*@ public normal_behavior
      @  ensures \result == \memoryArea(object);
      @  working_space 0;
      @*/
    public static /*@pure@*/ MemoryArea getMemoryArea(java.lang.Object object);

    /*@ normal_behavior
      @  working_space 0;
      @*/
    public /*@pure@*/ long memoryConsumed(){
	return consumed;
    }

    /*@ normal_behavior
      @  working_space 0;
      @  ensures \result==size-consumed;
      @*/
    public /*@pure@*/ long memoryRemaining(){
	return size-consumed;
    }

    /* public normal_behavior
      @  requires type==Byte.TYPE || type==Boolean.TYPE;
      @  working_space \space(new byte[number]);
      @ also public normal_behavior
      @  requires type==Short.TYPE || type==Char.TYPE;
      @  working_space \space(new short[number]);
      @ also public normal_behavior
      @  requires type==Long.TYPE;
      @  working_space \space(new long[number]);
      @ also public normal_behavior
      @  requires type!=Long.TYPE;
      @  working_space \space(new int[number]);
      @*/
    public java.lang.Object newArray(java.lang.Class type, int number){
	
    }
 
    /*    public java.lang.Object newInstance(java.lang.Class type)
	throws java.lang.InstantiationException,
	       java.lang.IllegalAccessException {}

    public java.lang.Object newInstance(java.lang.reflect.Constructor c, 
					java.lang.Object[] args) 
	throws java.lang.IllegalAccessException,
	       java.lang.InstantiationException,
	       java.lang.reflect.InvocationTargetException {}
    */
    public long size(){
	return size;
    } 
    

}
