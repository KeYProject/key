// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.util.install;

import java.awt.GraphicsEnvironment;
import java.io.File;

import javax.swing.JFrame;

public class Installer extends JFrame {

    public static void main ( String[] args ) {
	String os = System.getProperty ( "os.name" );
	String currentDir = System.getProperty ( "user.dir" );
	String defaultKeYHome = System.getProperty ( "user.home" ) + File.separatorChar;
	defaultKeYHome = ( defaultKeYHome == null ?  "" :  defaultKeYHome ) +
	    "KeY" + File.separator;
	String defaultKeYLib = defaultKeYHome + "key-ext-jars";
	String javaHome = System.getProperty ( "java.home" );

        if (javaHome.endsWith("jre")) 
            javaHome = javaHome.substring( 0, javaHome.lastIndexOf ( "jre" ) );
        
        if (os.toLowerCase().indexOf("mac")!=-1) {           
            if (javaHome.endsWith("Home"))
                javaHome = javaHome.substring( 0, javaHome.lastIndexOf ( "Home" ) );
        }
        
        
	System.out.println ( " Current :" + currentDir );
	System.out.println ( " KeYHome :" + defaultKeYHome );
	System.out.println ( " KeYLib :" + defaultKeYLib );
	System.out.println ( " java.home :" + javaHome );
	System.out.println ( " OS :" + os );

	boolean gui = true;

	if (args.length>0 && "--text".equals(args[0])) {
	    gui = false;
	} else {
	    try {
		if (GraphicsEnvironment.
		    getLocalGraphicsEnvironment().getScreenDevices() == null ||
		    GraphicsEnvironment.
		    getLocalGraphicsEnvironment().getScreenDevices().length==0) {
		    gui = false;
		}
	    } catch(Throwable err) {
		gui = false;
	    }
	}

	if (gui) {
	    new KeYInstallerGUI ( defaultKeYHome, defaultKeYLib, javaHome, currentDir, os ).
		start ();
	} else {
	    new KeYInstallerCmdLine ( defaultKeYHome, defaultKeYLib, javaHome, currentDir, os ).
		start ();
	}
    }

}
