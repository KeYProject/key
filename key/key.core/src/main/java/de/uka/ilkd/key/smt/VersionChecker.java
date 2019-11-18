// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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