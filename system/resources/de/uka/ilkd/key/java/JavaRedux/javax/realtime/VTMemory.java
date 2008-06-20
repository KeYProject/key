package javax.realtime;

public class VTMemory extends ScopedMemory{

    public VTMemory(long size){
	super(size);
    }

    public VTMemory(long initial, long maximum){
	super(maximum);
	if(initial<0 || initial>maximum) throw new IllegalArgumentException();
    }

    public VTMemory(long initial, long maximum, java.lang.Runnable logic){
	super(maximum, logic);
	if(initial<0 || initial>maximum) throw new IllegalArgumentException();
    }

    public VTMemory(long size, java.lang.Runnable logic){
	super(size, logic);
    }

    public VTMemory(SizeEstimator size){
	super(size);
    }

    public VTMemory(SizeEstimator size, java.lang.Runnable logic){
	super(size, logic);
    }

    public VTMemory(SizeEstimator initial, SizeEstimator maximum){
	super(maximum);
	if(initial==null || initial.getEstimate()<0 || 
	   initial.getEstimate()>maximum.getEstimate()){
	    throw new IllegalArgumentException();
	}
    }

    public VTMemory(SizeEstimator initial, SizeEstimator maximum, 
	     java.lang.Runnable logic){
	super(maximum, logic);
	if(initial==null || initial.getEstimate()<0 || 
	   initial.getEstimate()>maximum.getEstimate()){
	    throw new IllegalArgumentException();
	}
    }
 
    public java.lang.String toString(){
	return "(VTMemory) "+super.toString();
    } 

}
