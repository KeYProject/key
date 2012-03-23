// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;

public class ExternalProcessLauncher {
    	public final static int RESULT = 0;
    	public final static int ERROR  = 1;
    	public final static int EXIT_CODE = 2;
        private Process process;
        private Pipe pipe = new Pipe();
    public ExternalProcessLauncher() {
    	pipe.addListener(new PipeListener() {
			
			@Override
			public void messageIncoming(Pipe pipe, String message, int type) {
				System.out.println("Type "+type +": "+message);				
			}
		});
    }

	public String[] launch(String [] command,String initialMessage) throws Throwable {
	        int exitCode =0;
	        String [] result= new String[3];
	     	try{
	        ProcessBuilder builder = new ProcessBuilder();
	        for(String cmd : command)
	        System.out.print(cmd+" ");
            	builder.command(command);
               	process = builder.start();
            pipe.start(process.getInputStream(),
            		   process.getOutputStream(),
            		   process.getErrorStream());
      
            pipe.sendMessgage(initialMessage+"\n");
            exitCode = process.waitFor();
            
            result[ERROR] = read(process.getErrorStream());
        
            process.getErrorStream().close();   	
               	
	     	result[RESULT] = read(process.getInputStream());
	     	process.getInputStream().close();

		
	
	    
		result[EXIT_CODE] = Integer.toString(exitCode);	
	     	}finally{
	     	    if(process != null){
	     	       process.destroy();
	     	    }
	     	}	     	
		return result;			
	}
	
	private void startPipe(OutputStream output, InputStream input){
		 InputStreamReader reader = new InputStreamReader(input);
		
		 try {
	            char[] b = new char[1024];
	            int read = 1;
	            // As long as data is read; -1 means EOF
	            while (read > -1) {
	                // Read bytes into buffer
	                read = reader.read(b);
	                //System.out.println("read: " + new String(b));
	                if (read > -1) {
	                	System.out.print(b);
	                }
	            }
	        } catch (Exception e) {
	            // Something happened while reading or writing streams; pipe is broken
	            throw new RuntimeException("Broken pipe", e);
	        } finally {
	            try {
	                input.close();
	            } catch (Exception e) {
	            }
	            try {
	                output.close();
	            } catch (Exception e) {
	            }
	        }
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
