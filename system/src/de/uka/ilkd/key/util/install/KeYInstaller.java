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
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

/**
 * This class is an abstract installer for the binary version of KeY. The
 * installer UI itself is realised in subclasses in order to support
 * a graphical and a command line interface.
 */

public abstract class KeYInstaller {


    private static final String binaryPath = "bin";
    private static final String systemPath = "system";
    private static final String keyextjarsPath = "key-ext-jars";

    private static final String[] subdirs = { systemPath,
					      binaryPath,
					      keyextjarsPath };



    /** array with names of required library files */
    private static final String[] libraries = new String[] {
	"antlr.jar", "recoderKey.jar"
    };

    /* necessary environment information */

    /** the directory where your Java interpreter is installed */
    private String JAVA_HOME = "";
    /** the directory where key has to be installed */
    private String KEY_HOME = "";
    /** the directory where the key external libraries can be found */
    private String KEY_LIB = "";

    /** the underlying operation system, default linux */
    private String[] supportedOS = {"linux", "win"};
    private String os = "linux";

    private String keyJarPath = "";

    public KeYInstaller ( String keyHome,
			  String keyLib,
			  String javaHome,
			  String keyJarPath,
			  String os ) {

	keyHome ( keyHome );
	keyLib ( keyLib );
	javaHome ( javaHome );
	keyJarPath ( keyJarPath );

	if ( os != null &&
	     ( os.toUpperCase ().indexOf ( "WINDOWS" ) >= 0 ||
	       os.toUpperCase ().indexOf ( "WINNT" ) >= 0 ) ) {
	    this.os = supportedOS [1];
	} else {
	    this.os = supportedOS [0];
	}
    }

    // create strings setting the environment right

    private String replaceAll ( String text,
				String old,
				String replacement ) {

	StringBuffer result = new StringBuffer ( text );

	int idx = 0;

	while ( (idx = text.indexOf( old, idx ) ) != -1 ) {
	    result.replace( idx, idx + 1, replacement );
	}

	return result.toString();
    }

    /**
     *  creates a comment with the given content
     * for the installation OS
     */
    protected String comment ( String comment ) {
	if ( "linux".equals ( os ) ) {
            return "# " + replaceAll ( comment, "\n", "\n# " ) + "\n";
	} else { // windows is assumed
            return "rem " + replaceAll ( comment, "\n", "\r\nrem " ) + "\r\n";
	}
    }

    /**
     *  sets an envrionment variable to the given value
     * for the installation OS
     */
    protected String variable ( String variable, String value ) {
	if ( "linux".equals ( os ) ) {
	    return variable + "=\"" + value + "\"\n";
	} else { // windows is assumed
	    return "SET " + variable + "=" + value + "\r\n";
	}
    }


    /** creates preamble in script setting the environment variables */
    protected String environment ( ) {
	StringBuffer environment = new StringBuffer ( );

	environment.append ( "linux".equals ( os ) ? "#!/bin/sh \n" : "" );
	environment.append ( "win".equals ( os ) ? "@echo off \r\n" : "" );
	environment.append ( comment ( " KeY-Environment Settings " ) );
	environment.append ( variable ( "KEY_HOME", keyHome () ) );
	environment.append ( variable ( "KEY_LIB", keyLib () ) );
	environment.append ( variable ( "JAVA_HOME", javaHome () ) );

	return environment.toString();
    }

    // selection of the correct shell-script

    protected String startProverScriptPatternName ( ) {
	return "startProver_" + os;
    }

    protected String startProverScriptPatternPath ( ) {
	return "de.uka.ilkd.key.util.install."
	    .replace ( '.', File.separatorChar ) + startProverScriptPatternName ();
    }

    protected String startProverScriptFilePath ( ) {
	return binaryPath () + File.separatorChar  + startProverScriptFileName ();
    }

    protected String startProverScriptFileName ( ) {
	return "linux".equals ( os ) ? "startProver" : "startProver.bat";
    }

    // create directories


    /**
     * creates directory structure as used by key
     */

    public void mkdirs ( ) {
        for (String subdir : subdirs) {
            File f = new File(keyHome() + File.separatorChar + subdir);
            f.mkdirs();
        }
    }


    public void copy( File file, String to ) throws KeYInstallerException {

	File newFile = new File( to + File.separatorChar + file.getName () );
	if ( newFile.equals(file) ) return ;
	if ( newFile.exists() ) newFile.delete();

        FileInputStream fis  = null;
        FileOutputStream fos = null;
	try {
            fis = new FileInputStream(file);
            fos = new FileOutputStream(newFile);
            byte[] buf = new byte[1024];
            int i = 0;
            while((i=fis.read(buf))!=-1) fos.write(buf, 0, i);
	} catch ( IOException ioe ) {
	    throw new KeYInstallerException
		( "Error occured while copying \n" + file + "\n to \n" +
		  newFile + " \n due to:\n" + ioe );
	} finally {
	    try {
		if ( fis != null ) fis.close ();
		if ( fos != null ) fos.close();
	    } catch ( IOException ioe ) {
		throw new KeYInstallerException
		    ( "Error occured while closing streams :" + ioe );
	    }
	}
    }


    // write shellscript

    private void createStandAloneProverScript ( JarFile jarFile )
	throws KeYInstallerException {
	createFile ( environment (),
		     startProverScriptFilePath (),
		     startProverScriptPatternPath (),
		     jarFile );
    }


    public void generateScripts ( JarFile jarFile )
	throws KeYInstallerException {
	createStandAloneProverScript( jarFile );
    }

    private void createFile ( String preamble,
			      String fileNameToWrite,
			      String fileNameToReadFromJar,
			      JarFile jarFile )
	throws KeYInstallerException {


	// write preamble
	FileOutputStream fw = null;
	InputStream in = null;
	try {
	    fw = new FileOutputStream ( new File ( fileNameToWrite ) );
	    fw.write ( preamble.getBytes () );

	    // rest of the start script
	    JarEntry entry = ( JarEntry ) jarFile.getEntry ( fileNameToReadFromJar.replace
		( File.separatorChar, '/' ) );

	    if ( entry == null ) {
		throw new KeYInstallerException ( " Could not found jar file entry : " +
						  fileNameToReadFromJar );
	    }
	    in = jarFile.getInputStream ( entry );

	    if ( entry.getSize () > Integer.MAX_VALUE ) {
		throw new KeYInstallerException
		    ( "Entry " + entry + " too big. Overflow would occur." );
	    }

	    byte[] scriptfileContent = new byte [ (int) entry.getSize() ];

	    long count = 0;
	    while ( count < scriptfileContent.length &&
		    in.available () != 0 ) {
		int bytesRead = in.read
		    ( scriptfileContent,
		      (int) count,
		      (int) ( scriptfileContent.length - count ) );
		count += ( bytesRead >= 0 ? bytesRead : 0 );
	    }

	    if ( count < scriptfileContent.length ) {
		throw new KeYInstallerException ( "Read " + entry +
						  " only partial ");
	    }

	    fw.write ( scriptfileContent );


	} catch ( IOException io ) {
	    throw new KeYInstallerException ( io.getLocalizedMessage () );
	} finally {
	    try {
		if ( in != null ) { in.close(); }
		if ( fw != null ) { fw.close(); }
	    } catch ( IOException io ) {
		throw new KeYInstallerException ( io.getLocalizedMessage () );
	    }
	}
    }

    protected void extractExamples(JarFile jarFile) throws IOException {
        File targetDir = new File(keyHome(), "examples" + File.separatorChar + "firstTouch");
        Enumeration<JarEntry> en = jarFile.entries();
        while(en.hasMoreElements()) {
            JarEntry entry = ((JarEntry)en.nextElement());
            File file = new File(targetDir, entry.getName());
            if (entry.isDirectory()) {
                if (!file.exists()) {
                    file.mkdirs();
                }
            } else {
                InputStream in = jarFile.getInputStream(entry);
                FileOutputStream out = new FileOutputStream(file);
                byte[] buf = new byte[1024];
                int i = 0;
                while ((i = in.read(buf)) != -1) {
                    out.write(buf, 0, i);
                }
                out.close();
                in.close();
            }
        }
    }

    // jar helper methods

    /**
     * Extracts files from the key/program jar-archive.
     * @param entrypath name of the file in the jar
     * @param filename name to be copied to.
     */
    public void extractFromJar( String  entrypath,
			        String  writetopath,
			        String  filename,
			        JarFile jarFile )
    throws KeYInstallerException {
	try {
	    //generate directories to write file:
	    boolean dirs = (new File(writetopath)).mkdirs();

	    // get JarEntry
	    JarEntry entry = (JarEntry) jarFile.getEntry( entrypath +
							  '/' +
							  filename );
	    if ( entry == null ) {
		throw new KeYInstallerException ( " Could not find jar file entry : " +
						  entrypath + '/' +
						  filename );
	    }

	    InputStream in = jarFile.getInputStream(entry);
	    //Write to file
	    FileOutputStream out = new FileOutputStream( writetopath +
							 File.separatorChar +
							 filename );
	    int c;
	    while ( ( c = in.read () ) != -1 ) {
		out.write ( c );
	    }
	    out.close ();
	    in.close ();
	} catch ( IOException ioe ) {
	    throw new KeYInstallerException ( " IOException occurred when trying to extract from jar file. " +
					      jarFile, ioe );
	}
    }

    /** Checks if libraries are found in the keyLib directory
     * and returns a list of missing files
     */
    public String[] checkLibraries () {
	LinkedList<String> l = new LinkedList<String> ();
	for ( int i = 0; i < libs ().length; i++ ) {
	    File lib = new File ( keyLib () + File.separatorChar + libs () [i] );
	    if ( ! lib.exists() ) {
		l.add ( keyLib () + File.separatorChar + libs () [i] );
	    }
	}
	return ( String [] ) l.toArray ( new String [l.size ()] );
    }


    // some getters

    /**
     * returns the names of the required libraries
     */
    public String[] libs () {
	return libraries;
    }

    /**
     * returns directory of JAVA_HOME
     */
    public String javaHome () {
	return JAVA_HOME;
    }

    /**
     * returns directory of KEY_HOME
     */
    public String keyHome () {
	return KEY_HOME;
    }

    /**
     * returns directory of KEY_LIB
     */
    public String keyLib () {
	return KEY_LIB;
    }

    /**
     * returns list of all supported os
     */
    public String[] supportedOS () {
	return supportedOS;
    }

    /**
     * returns installation os
     */
    public String os () {
	return os;
    }


    /**
     * returns subdirectory where to put the (shell) scripts
     */
    public String binaryPath () {
	return keyHome () + File.separatorChar + binaryPath;
    }

    /**
     * returns directory where to put the system
     * (jar file)
     */
    public String systemPath () {
	return keyHome () + File.separatorChar + systemPath;
    }

    /**
     * returns directory where to put the system
     * libraries ( per default )
     */
    public String keyextjarsPath () {
	return keyHome () + File.separatorChar + keyextjarsPath;
    }

    /**
     * returns directory where to find key.jar
     */
    public String keyJarPath () {
	return keyJarPath;
    }

    /**
     * returns file where to find key.jar
     */
    public String keyJarFile () {
	return keyJarPath () + File.separatorChar + "key.jar";
    }

    // some setters

    /**
     * sets os; has to be one of supportedOS
     */
    public void os ( String os ) {
	this.os = os;
    }

    /**
     * sets directory of JAVA_HOME
     */
    public void javaHome ( String dir ) {
	JAVA_HOME = trail ( dir ) ;
    }

    /**
     * remove trailing file separatorchars
     */
    private String trail ( String dir ) {
	String result = dir;
	while ( result.length () > 0 &&
		result.charAt ( result.length () -1 ) == File.separatorChar )  {
	    result = result.substring ( 0, result.length () - 1 );
	}

	return result;
    }


    /**
     * sets directory of KEY_HOME
     */
    public void keyHome ( String dir ) {
	KEY_HOME = trail ( dir );
    }

    /**
     * sets directory of KEY_LIB
     */
    public void keyLib ( String dir ) {
	KEY_LIB = trail ( dir );
    }

    /**
     * sets directory where to find key.jar
     */
    public void keyJarPath ( String dir ) {
	keyJarPath = trail ( dir );
    }

    /**
     * entry method
     */
    public abstract void start ();

    /*
      Vorgehen:
          1. Begruessung
	  2. Verzeichnis, in das KeY installiert werden soll angeben lassen
	  3. Verzeichnis, in dem die KeY-Bibliotheken gesucht werden sollen
	     angeben lassen
	  4. existiert das Verzeichnis nicht, anlegen und den
	     Benutzer auffordern die Bibliotheken dort hinein zu
	     kopieren (mgl. das zu ueberspringen
	     nur mit ausdruecklichem "I will do it later").
	  5. Dateien kopieren
	  6. Fertig.
     */

}

