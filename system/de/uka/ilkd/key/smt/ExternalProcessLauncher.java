package de.uka.ilkd.key.smt;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

public class ExternalProcessLauncher {
    	public final static int RESULT = 0;
    	public final static int ERROR  = 1;
    	public final static int EXIT_CODE = 2;
        private Process process;

	public String[] launch(String [] command) throws Throwable {
	        int exitCode =0;
	        String [] result= new String[3];
	     	try{
	        ProcessBuilder builder = new ProcessBuilder();
            	builder.command(command);
               	process = builder.start();
            	exitCode = process.waitFor();
            	
	     	result[RESULT] = read(process.getInputStream());
	     	process.getInputStream().close();

		
		result[ERROR] = read(process.getErrorStream());
		process.getErrorStream().close();
	    
		result[EXIT_CODE] = Integer.toString(exitCode);	
	     	}finally{
	     	    if(process != null){
	     	       process.destroy();
	     	    }
	     	}	     	
		return result;			
	}
	
	public void stop(){
	    process.destroy();
	}
	
	    /** Read the input until end of file and return contents in a
	     * single string containing all line breaks. */
	    static String read(InputStream in) throws IOException {
		BufferedReader reader = new BufferedReader(new InputStreamReader(in));
		StringBuffer sb = new StringBuffer();

		int x = reader.read();
		while (x > -1) {
		    sb.append((char) x);
		    x = reader.read();
		}
		return sb.toString();
	    }

	
}
