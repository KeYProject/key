package javax.realtime;

public class ImmortalMemory extends MemoryArea{

    /*@ public static invariant instance!=null && 
      @          \memoryArea(instance)==instance && 
      @          instance.parent==instance &&
      @          \inImmortalMemory(instance); 
      @*/
    private static ImmortalMemory instance;

    public void	executeInArea(java.lang.Runnable logic){
	super.executeInArea(logic);
	/*	if(logic==null) throw new IllegalArgumentException();
		logic.run();*/
    }

    /*@ public normal_behavior
      @  assignable \nothing;
      @  ensures \result == instance;
      @*/
    public static /*@pure@*/ ImmortalMemory instance(){
	return instance;
    }

}
