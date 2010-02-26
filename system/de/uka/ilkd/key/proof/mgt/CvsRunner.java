// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


// CvsRunner.java
// $Id: CvsRunner.java 1.4.1.9.1.2.1.3.1.3 Wed, 23 Aug 2006 17:11:07 +0200 richard $  
// (c) COPYRIGHT MIT and INRIA, 1997.
// Please first read the full copyright statement in file COPYRIGHT.html
// http://dev.w3.org/cvsweb/java/classes/org/w3c/cvs/CvsRunner.java

// Contains code from com.ice.jcvslet.JCVSletLog by Tim Endres, time@gjt.org



package de.uka.ilkd.key.proof.mgt;

import java.io.*;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.util.Debug;



public class CvsRunner {
//    private static final File tmpdir = new File("/tmp");
    public static boolean debug = true;
    
    private static final String REP_ROOT = PathConfig.KEY_CONFIG_DIR+File.separator+"CVS-PO-REP"+
       File.separator;
//    private static final String ROOT_OPT = "-d "+REP_ROOT;

    private Logger mgtLogger = Logger.getLogger("key.proof.mgt");
    

    /**
     * Dump the given string into a temporary file.
     * This is used for th <code>-f</code> argument of the cvs commit command.
     * This method should only be used from a synchronized method.
     * @param string The string to dump.
     */

    File getTemporaryFile (String string) 
	throws CvsException
    {
	// Create a pseudo-random temporary filename
	String fn = "cvs-" + System.currentTimeMillis()+"-"+string.length();
	File temp = null;
	try {
	    temp = File.createTempFile (fn, "-"+string.length()) ;
	    temp.deleteOnExit();
	    PrintStream out  = new PrintStream (new FileOutputStream(temp)) ;
	    out.print(string) ;
	    out.close() ;
	    return temp ;
	} catch (IOException ex) {
	    error ("temporaryFile"
		   , "unable to create/use temporary file: " 
		   + (temp == null ? "(creation failed)" : temp.getAbsolutePath())) ;
	}
	return temp ;
    }

    /**
     * Emit an error.
     * Some abnormal situation occured, emit an error message.
     * @param mth The method in which the error occured.
     * @param msg The message to emit.
     * @exception CvsException The exception that will be thrown as a 
     *     result of the error.
     */

    protected void error (String mth, String msg) 
	throws CvsException
    {
	String emsg = this.getClass().getName()+"["+mth+"]: "+msg ;
	throw new CvsException (emsg) ;
    }

    /**
     * Get a filename between quote contained in this String.
     * @return the filename of null.
     */
    protected String getQuotedFilename(String line) {
	int idx = line.indexOf('\'');
	if (idx == -1)
	    return null;
	char ch;
	StringBuffer buffer = new StringBuffer();
	try {
	    while ( (ch = line.charAt(idx++)) != '\'' )
		buffer.append(ch);
	} catch (ArrayIndexOutOfBoundsException ex) 
	    {Debug.out("Exception thrown by class CsvRunner at buffer.append()");}
	return buffer.toString();
    }

    /**
     * Wait for the underlying CVS process to finish.
     * Once the process is terminated, all relevant streams are closed, and
     * an exception if potentially thrown if the process indicated failure.
     * @param proc The CVS process.
     * @param ccode Should we expect a zero status from the child process.
     * @exception CvsException If a zero status is expected, and the CVS
     * @return true iff operation successful
     * process exit status is not zero.
     */

    protected synchronized boolean waitForCompletion (ProcessEnvironment proc,
                                                      boolean ccode)
    throws CvsException {
        proc.waitForTermination ();

        //no exception thrown, that's an unknown exception.
        int ecode = proc.proc.exitValue ();
        if ( ecode != 0 ) {
            String msg = ( "Process exited with error code: " + ecode
                           + " error [" + proc.errorLog + "]" );
            if ( debug ) mgtLogger.error ( msg );
            if ( ccode ) {               
                throw new CvsException ( msg );
            }
            return false;
        }
        return true;

    }




    public boolean cvsImport(String moduleName, String workingDir,
                             String vendorTag, String releaseTag)
	                                   throws CvsException {	
        initRep();
	String[] command = new String[] {
            "cvs" , "-d", REP_ROOT , "import", "-d",
            "-I","*.tpr", "-I","*.tws", "-I","*.df*", "-I","*.txv*",
            "-m", "your.message.here",
            moduleName, vendorTag.replace(' ','_'), releaseTag};
	// Run it:
	try {
	    mgtLogger.info("Executing "+print(command)+" in "+workingDir);
	    return waitForCompletion
	    ( new ProcessEnvironment ( Runtime.getRuntime ().exec ( command,
	                                                            null,
	                                                            new File ( workingDir ) ) ),
                                       false );
	} catch (IOException ex) {
	    ex.printStackTrace();
	    throw new CvsException(ex.getMessage());
	}
    }
    

/*    
    public void cvsLog(String moduleName) throws CvsException {
	String command = "/usr/bin/cvs " + ROOT_OPT + " rlog -h "+ moduleName;
	// Run it:
	try {
	    mgtLogger.info("Executing "+command);
	    ProcessEnvironment proc =
	        new ProcessEnvironment ( Runtime.getRuntime().exec(command) );
            parseLogOutput(proc.proc.getInputStream());
	    waitForCompletion(proc, false);
	} catch (IOException ex) {
	    ex.printStackTrace();
	    throw new CvsException(ex.getMessage());
	}
    }
*/


    public String cvsDiff(String moduleName, String tag1, String tag2) 
                                                     throws CvsException {
	String[] command = new String[] {
            "cvs", "-d", REP_ROOT, "rdiff", "-u",
            "-r", tag1, "-r", tag2, moduleName};
        String s = "";
	// Run it:
	try {
	    mgtLogger.info("Executing "+print(command));
	    ProcessEnvironment proc =
	        new ProcessEnvironment ( Runtime.getRuntime().exec(command, null, 
	                      new File(System.getProperty("user.home"))) );
	    BufferedReader in   = new BufferedReader(
               new InputStreamReader(proc.proc.getInputStream()));
            String         line = null ;
            while ((line = in.readLine()) != null) {
                // Make sure the line isn't empty:
                if ( line.length() <= 0 ) continue;
                s += line+"\n";
            }
            waitForCompletion ( proc, true );
	} catch (IOException ex) {
	    ex.printStackTrace();
	    throw new CvsException(ex.getMessage());
	}
        mgtLogger.debug("Diff:\n"+s);        
        return s;
    }


    private void parseLogOutput(InputStream procin) 
        throws IOException {
        
        boolean collectSymbols = false;
    
	BufferedReader in   = new BufferedReader(new InputStreamReader(procin));
        String         line = null ;
        while ((line = in.readLine()) != null) {
            // Make sure the line isn't empty:
            if ( line.length() <= 0 ) continue;


            if ( collectSymbols ) {
                if ( line.startsWith( "\t" ) ) {
                    String symStr = line.substring(1);
                    int colonPos = symStr.indexOf(':');
                    symStr = symStr.substring(0,colonPos).trim();
                    mgtLogger.debug("CVS Symbols: "+ symStr );
                } else {
                    collectSymbols = false;
                }
            } else 
               if (line.startsWith( "symbolic names:" )) collectSymbols = true;

            
        }
    }
    
    
    private void initRep() throws CvsException {
       File rep = new File(REP_ROOT+File.separator+"CVSROOT");
       File anchor = new File(PathConfig.KEY_CONFIG_DIR+File.separator+"CVS_ANCHOR_DIR"+
                              File.separator+"KEY_CVS_ANCHOR");
                           
       try {
           if (!rep.exists()) {
              rep.mkdirs();
	      String[] command = new String[] {
                  "cvs", "-d", REP_ROOT, "init"};
	      // Run it:
	          mgtLogger.info("Executing "+print(command));
	          Process proc =  Runtime.getRuntime().exec(command);
	          waitForCompletion(new ProcessEnvironment (proc), false);
           }

//           if (!anchor.exists()) anchor.createNewFile();
       } catch (IOException ex) {
	   ex.printStackTrace();
	   throw new CvsException(ex.getMessage());
       }
    
    }
    
    
    private String print(String[] arr) {
        StringBuffer s = new StringBuffer(300);
        for (String anArr : arr) s.append(anArr);
        return s.toString();
    }
    
    
    
    
    


    /**
     * Thread that reads data from a given input stream and stores it in a
     * string buffer
     */
    private static class StreamReaderThread extends Thread {
        private final StringBuffer log;
        private final InputStream procin;
        
        public StreamReaderThread (final StringBuffer log, final InputStream in) {
            this.log = log;
            this.procin = in;
        }
        
        public void run () {
            BufferedReader in = new BufferedReader ( new InputStreamReader ( procin ) );
            String line = null;

            try {
                while ( ( line = in.readLine () ) != null ) {
                    log.append ( line + "\n" );
                }
            } catch ( IOException ex ) {
                ex.printStackTrace ();
            }
            
            synchronized ( this ) {
                notifyAll ();
            }
        }
        
        public synchronized void waitForTermination () {
            while ( isAlive() ) {
                try {
                    wait ();
                } catch ( InterruptedException e ) {
                    Debug.out("Exception thrown by class CvsRunner at IO: ", e);
                }
            }
        }
    }


    /**
     * Encapsulate a given process object. By default a thread is spawn that
     * handles error output of the process, to ensure that pending error output
     * does not block the process. Error output is stored in a string buffer and
     * can be accessed after termination of the process. 
     */
    private static class ProcessEnvironment {
        public final Process proc;
        public final StringBuffer errorLog;
        
        private final StreamReaderThread errReader;
        
        public ProcessEnvironment (final Process proc) {
            this.proc = proc;
            errorLog = new StringBuffer ();
            errReader = new StreamReaderThread ( errorLog,
                                                 proc.getErrorStream () );
            errReader.start ();
        }

        /**
         * Wait for the termination of the process. To this end further standard
         * output the process produces is read and discarded. 
         */
        public void waitForTermination () {
            final StreamReaderThread stdReader =
                new StreamReaderThread ( new StringBuffer (),
                                         proc.getInputStream () );
            stdReader.start ();
            errReader.waitForTermination();
            stdReader.waitForTermination();
            try {
                proc.waitFor();
            } catch ( InterruptedException e ) {
                Debug.out("Exception thrown by class CvsRunner at IO: ", e);
            } finally {                
                // Close all streams, just to make sure...
                try { proc.getInputStream().close(); } 
                catch (Exception ex) {Debug.out("Exception thrown by class CvsRunner at IO-close");}
                try { proc.getOutputStream().close(); } 
                catch (Exception ex) {Debug.out("Exception thrown by class CvsRunner at IO-close");}
                try { proc.getErrorStream().close(); } 
                catch (Exception ex) {Debug.out("Exception thrown by class CvsRunner at IO-close");}
            }
        }
    }

}
