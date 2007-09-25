package javax.realtime;

public class LTMemory extends ScopedMemory{

    public LTMemory(long size){
	super(size);
    }

    public LTMemory(long initial, long maximum){
	super(maximum);
	if(initial<0 || initial>maximum) throw new IllegalArgumentException();
    }

    public LTMemory(long initial, long maximum, java.lang.Runnable logic){
	super(maximum, logic);
	if(initial<0 || initial>maximum) throw new IllegalArgumentException();
    }

    public LTMemory(long size, java.lang.Runnable logic){
	super(size, logic);
    }

    public LTMemory(SizeEstimator size){
	super(size);
    }

    public LTMemory(SizeEstimator size, java.lang.Runnable logic){
	super(size, logic);
    }

    public LTMemory(SizeEstimator initial, SizeEstimator maximum){
	super(maximum);
	if(initial==null || initial.getEstimate()<0 || 
	   initial.getEstimate()>maximum.getEstimate()){
	    throw new IllegalArgumentException();
	}
    }

    public LTMemory(SizeEstimator initial, SizeEstimator maximum, 
	     java.lang.Runnable logic){
	super(maximum, logic);
	if(initial==null || initial.getEstimate()<0 || 
	   initial.getEstimate()>maximum.getEstimate()){
	    throw new IllegalArgumentException();
	}
    }
 
    public java.lang.String toString(){
	return "(LTMemory) "+super.toString();
    } 

}
