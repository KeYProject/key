package javax.realtime;

public abstract class MemoryArea{

    protected final long size;
    protected long consumed;
    protected final /*@ nullable @*/ Runnable logic;

    protected final PhysicalMemoryArea memory;

    protected MemoryArea(long size){
	this(size, null);
    }

    protected MemoryArea(long size, java.lang.Runnable logic){
	if(size<0) throw new IllegalArgumentException();
	this.size = size;
	this.logic = logic;
	memory = new PhysicalMemoryArea(size);
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
	memory = new PhysicalMemoryArea(this.size);
    }

    private void <runRunnable>(java.lang.Runnable logic){
	logic.run();
    }

    public void enter(){
	if(logic==null) throw new IllegalArgumentException();
	<runRunnable>(logic);
    }

    public void enter(java.lang.Runnable logic){
	if(logic==null) throw new IllegalArgumentException();
	<runRunnable>(logic);
    }

    public void executeInArea(java.lang.Runnable logic){
	if(logic==null) throw new IllegalArgumentException();
	<runRunnable>(logic);
    }

    public static MemoryArea getMemoryArea(java.lang.Object object){
	return object.memoryArea;
    }

    /*@ normal_behavior
      @  working_space 0;
      @*/
    public /*@pure@*/ long memoryConsumed(){
	return consumed;
    }

    /*@ normal_behavior
      @  working_space 0;
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
