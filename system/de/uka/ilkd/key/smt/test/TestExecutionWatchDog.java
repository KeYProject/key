package de.uka.ilkd.key.smt.test;

import java.io.IOException;
import java.util.Date;
import java.util.Timer;

import junit.framework.TestCase;
import de.uka.ilkd.key.smt.ExecutionWatchDog;

public class TestExecutionWatchDog extends TestCase {

    
    public void testWatchdog() {
	boolean wasInterrupted = false;
	boolean notExecuteable = false;
	try {
	    Process p = Runtime.getRuntime().exec("yices");
	    ExecutionWatchDog wd = new ExecutionWatchDog(1, p);
	    Timer t = new Timer();
	    t.schedule(wd, new Date(System.currentTimeMillis()), 1000);
	    try {
		//System.out.println("waiting");
		int i = p.waitFor();
		//System.out.println("Result from waiting: " + i);
		wasInterrupted = wd.wasInterrupted();
	    } catch (InterruptedException e) {
		wasInterrupted = true;
	    }
	} catch (IOException e) {
	    System.out.println("IOException thrown");
	    System.out.println(e.getMessage());
	    notExecuteable = true;
	}
	assert(wasInterrupted | notExecuteable);
    }
    
}
