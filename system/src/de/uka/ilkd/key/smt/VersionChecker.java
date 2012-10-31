package de.uka.ilkd.key.smt;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.Timer;
import java.util.TimerTask;

/**
 * Little helper class that helps to check for the version of a solver. Mainly it provides 
 * a method that starts the solver using certain parameters in order to obtain the version of that
 * solver.
 */
public class VersionChecker {
	public static final VersionChecker INSTANCE = new VersionChecker();
	
	private static final long  maxDelay = 1000;
	
	public String getVersionFor(String command, String parameter){
		ProcessBuilder pb = new ProcessBuilder(command,parameter);
		Process p = null;
		Timer timer = new Timer(true);
		try{
			final Process process = pb.start();
			p = process;
			timer.schedule(new TimerTask() {
			
			@Override
			public void run() {
				process.destroy();
			}
			}, maxDelay);
			return new BufferedReader(new InputStreamReader(p.getInputStream())).readLine(); 
		}catch(Throwable e){
			throw new RuntimeException(e);
		}finally{
			if(p != null){
				p.destroy();
			}
		}
	}
}
