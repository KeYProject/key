// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.util.install;


import java.io.*;
import java.util.jar.JarFile;

/** 
 * This class is a command line UI for installing KeY
 */

public class KeYInstallerCmdLine extends KeYInstallerUI {
    
    public KeYInstallerCmdLine ( String keyHome, 
				 String keyLib, 
				 String javaHome, 
				 String keyJarPath,			  
				 String os ) {

	super ( keyHome, keyLib, javaHome, keyJarPath, os );	
    }

    
    // ASCII rendering    
    public String makeTitle ( String title ) {

	StringBuffer separator = new StringBuffer ();

	for ( int i = 0; i < title.length(); i++ ) {
	    separator.append("=");
	}

	return title + "\n" + separator + "\n\n";
    }


    // input methods
    
    /**     
     * reads input line until a character is read in, that also occurs in the
     * given list of characters. 
     * @return the read character
     */
    public char expect ( char[] expectedChars )  {
	
	char result = (char) -1;
	try {
	    char c;	    

	    while ( ! containsChar ( ( c = (char) System.in.read () ) ,
				     expectedChars ) ){}
	    result = c;
	} catch ( IOException io ) {	    
	    criticalError ( "Could not read from standard input stream.",
			    io );
	    System.exit ( -1 );
	}

	return result;       
    }

    public void pause() {
	System.out.println( "Press <ENTER> to proceed:" );
	expect ( new char [] { '\n' } );
    }

    protected String readLine () {

	String result = "";

	try {

	    if ( System.in.available() > 0 ) { // flush keyboard buffer
		System.in.read ( new byte [System.in.available()] );
	    }

	     result = new BufferedReader 
		 ( new InputStreamReader ( System.in ) ).readLine ();

	} catch ( IOException io ) {	    
	    criticalError ( "Could not read from standard input stream.",
			    io );
	    System.exit ( -1 );
	}
	
	return result;
	    
    }

    public String readDir ( boolean hasToExist ) {
	
	String dir = "";
	
	boolean correct;
	do {
	    correct = true;
	    dir = readLine ();       	

	    File f = new File ( dir );

	    if ( ! f.isDirectory () && f.exists () ) {
		print ( "Directory required." );
		correct = false;
	    }		
	    if ( hasToExist &&  !f.exists () ) {
		print ( "Directory does not exist." );
		correct = false;
	    }
	} while ( ! correct );	
	
	return dir;
    }

    // helpers

    public final void print ( String s ) {
	System.out.println ( s );
    }


    // text
    protected String title () {
	return "Welcome";
    }

    protected String welcome () {
	String welcome = 
	    "Dear User,\n"+
	    "   thank you for choosing KeY. In case of any questions, problems " +
	    "or suggestions please contact us: mailto:key@ira.uka.de\n" +  
	    "We would also be interested to know for which purpose you will use "+
	    " KeY, e.g. research, industry or teaching.\n" + 
	    "\t Best regards,\n"+
	    "\t    Your KeY-Team";
	return welcome;
    }

    protected String titleGlobals () {
	return " General Settings ";
    }
    
    protected String globals () {
	String globals = "";
	
	globals += "Directory where to install KeY."; 
	globals += "\n(1) KEY_HOME : " + 
	    ( "".equals ( keyHome () ) ? "(none)" : keyHome () );
		
	globals += "\nDirectory, where your Java is installed "; 
	
	globals += "\n(2) JAVA_HOME : " +  
	    	    ( "".equals ( javaHome () ) ? "(none)" : javaHome () );

	globals += "\n(c)ontinue";

	globals += "\nPress 1 or 2 to enter a directory, c for continue:";

	return globals;
    }

    protected String titleLibrary () {
	return " Library Settings ";
    }
   

    protected String library () {
	String library = " KeY makes use of different external libraries.";
	
	library += "For download and additional information see ";
	library += "http://download.key-project.org";
	library += "You have to install them in ONE directory (usually: ";
	library += keyextjarsPath () + "). Enter below the directory ";
	library += "where KeY looks for them.\n";
	library += "Library Path:"; 
	library += "\n(1) KEY_LIB : " + 
	    ( "".equals ( keyLib () ) ? "(none)" : keyLib () );
	
	library += "\n(c)ontinue";

	library += "\nPress 1 to enter the library directory, c for continue : ";

	return library;
    }
    
    public String[] checkLibraries () {

	String[] missingLibs = super.checkLibraries ();

	char c = '1';

	while ( ( missingLibs.length != 0 ) && c  != '2' ) {

	    StringBuffer missing = 
		new StringBuffer ( "The following libraries are missing:\n" );
        for (String missingLib : missingLibs) {
            missing.append(missingLib);
            missing.append("\n");
        }
	    
	    missing.append ( "Please copy them to " );
	    missing.append ( keyLib () );
	    missing.append ( "\n" );
	    missing.append ( "(1) I have copied them " );
	    missing.append ( "(2) I will copy them later and promise to spend " + 
			     "you a beer at the next conference, if I forget it." );       
	    
	    print ( trim ( missing.toString (), 72 ) );
	    switch ( c ) {
	    case '1' : 
		missingLibs = super.checkLibraries ();
		break;
	    }
	    
	    c = expect ( new char[] { '1', '2' } );
	}

	return missingLibs;
    }

    // main methods
    
    public void start () {				

 	StringBuffer todo = new StringBuffer("");
	String [] missingLibs = new String [0];

	print ( makeTitle ( title () ) );		

	print ( trim ( welcome (), 72 ) );

	pause ();	
	
	File keyJar = new File ( keyJarFile () );
	while ( ! keyJar.exists ()  ) {
	    print ( trim ( "Have not found file 'key.jar' in " + keyJarPath () + 
			   ". Please enter the directory where you have " + 
			   "put key.jar (usually the directory where you " + 
			   "have unpacked key): " , 72 ) );
	    keyJarPath ( readDir ( true ) );
	    keyJar = new File ( keyJarFile () );
	}
	
	JarFile keyJarFile = null;
	try {
	    keyJarFile = new JarFile ( keyJar );
	} catch ( FileNotFoundException fne ) {	    
	    error ( "Did not found a valid jarfile at " + keyJarPath () + 
		    " Please check if it is there and " + 
		    "if you have read and write access.\n Detail: " + fne );
	    System.exit ( -1 );
	} catch ( IOException ioe ) {
	    error ( "Error when trying to access 'key.jar' at " + keyJarPath () + 
		    ".\n Detail: " + ioe );	    
	    System.exit ( -1 );
	}

	print ( makeTitle ( titleGlobals () ) );
	
	char [] options = new char [] { '1', '2', 'c' }; 
	char c;
	print ( trim ( globals (), 72 ) );
	while ( ( c = expect ( options  ) ) != 'c' ) {
	    switch ( c ) {
	    case '1' : 
		print ( "KEY_HOME : " );
		keyHome ( readDir ( false ) );
		keyLib  ( keyHome () + File.separatorChar + "key-ext-jars" ); 
		break;
	    case '2' : 
		print ( "JAVA_HOME : " );
		javaHome ( readDir ( true ) );
		break;
	    default : 
		print ( "\n Wrong character (expected : 1,..,4 or c). Re-enter :");
		break;
	    }
	    print ( trim ( globals (), 72 ) );	    
	} 		

	print ( makeTitle ( titleLibrary () ) );

	print ( trim ( library (), 72 ) );

	while ( ( c = expect ( new char [] { '1', 'c' }  ) ) != 'c' ) { 
	    switch ( c ) {
	    case '1' : 
		print ( "KEY_LIB : " );	       		
		keyLib ( readDir ( false ) );
		missingLibs = checkLibraries ();
		break;
	    default : 
		print ( " Wrong character (expected : 1 or c).");
		break;
	    }
	    print ( trim ( library (), 72 ) );
	}
		
	mkdirs ();	

	try {
	    generateScripts ( keyJarFile );
	} catch ( KeYInstallerException kie ) {
 	    error ( "Could not generate the shell scripts. Please " + 
 		    "resolve the problem first " + 
 		    "and redo the installation afterwards.\n Detail: " + kie );
 	    System.exit ( -1 );
 	}

        File examplesFile = new File(keyJarPath(), EXAMPLES_JAR_FILE);
        try {
            JarFile examplesJarFile = new JarFile(examplesFile);
            extractExamples(examplesJarFile);
        } catch (IOException e) {
            todo.append("Could not unpack the examples. Please " +
                    "resolve the problem first " +
                    "and redo the installation afterwards.\nDetail:" + e);
        }

	if ( "linux".equals ( os () ) ) {
	    try {
		Runtime.getRuntime ().exec ( "chmod a+x " + startProverScriptFilePath () );
	    } catch ( IOException e) { 
		todo.append ( "Please set " + startProverScriptFilePath () +  
			      " executable : chmod a+x " + startProverScriptFilePath ());
		todo.append ( "\n" );
	    }
	}

	try {
	    copy( keyJar, systemPath () );
	} catch ( KeYInstallerException kie ) {
	    todo.append ( " Copy file 'key.jar' from " + keyJar + 				
			  " to " + systemPath () + 
			  "\n\t usually this should be done automatical, " + 
			  "but failed due to: " + kie );
	    todo.append ( "\n" );
	}

	if ( missingLibs.length > 0 ) {
	    todo.append ( "Please copy the following libraries to" );
	    todo.append ( keyLib () );
	    for ( int i = 0; i < missingLibs.length; i++ ) {
		todo.append ( "\n" );
		todo.append ( i + ". " + missingLibs [i] );
	    }
	    todo.append ( "\n" );
	} 
   
//	File examplesJarFile = new File(keyJarPath(), EXAMPLES_FILE);
//	if(examplesJarFile.canRead()) {
//		extract(examplesJarFile, keyHome());
//	} else {
//		todo.append("Cannot extract " + EXAMPLES_FILE + " containing the KeY examples. " +
//				"Please install them manually if you want to use them.\n");
//	}

	if ( todo.length () > 0 ) {
	    print ( trim ( "Some things are left to do. Please read carefully.", 72 ) );
	    print ( trim ( todo.toString (), 72 ) );
	    print ( trim ( "After you have done the things above, you can start KeY." + 
			   "To do this, you have to change to directory " + binaryPath () + 
			   "and execute " + startProverScriptFileName (), 72 ) );
	} else 
	    print ( trim ( "Installation finished. To start change to directory"
			   + " " + binaryPath () + 
			   " and execute " + startProverScriptFileName (), 72 ) );
	    print ( trim ( "Typical examples for KeY can be opened from 'Load Examples' " +
	    		"in the 'File' menu.", 72 ) );
    }


// error handling

    private void error ( String msg ) {
	System.err.println ( makeTitle ( "An Error Occured." ) ); 
	System.err.println ( trim ( "Error Description:" + msg, 72 ) );
    }

    private void criticalError ( String msg, Exception e ) {
       System.err.println ( makeTitle ( "A Critical Error Occured." ) ); 
       System.err.println ( trim ( "Error Description:" + msg, 72 ) );
       System.err.println 
	   ( "A critical error has occured. Please send a bug "+
	     "report to: key@ira.uka.de\n" +  
	     "The bug report should include:\n" + 
	     "\t Error Classification " /*+ ": Developer Heart Attack"*/ + "\n" +
	     "\t Operating system \n" + 
	     "\t Java Version \n" + 
	     "\t Steps to reproduce ( if possible ) \n" + 
	     "\t and the following error message: \n" +
	     e.getLocalizedMessage () );
       e.printStackTrace ();
    }
}
