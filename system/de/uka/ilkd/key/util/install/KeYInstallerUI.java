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


public abstract class KeYInstallerUI extends KeYInstaller {


    public KeYInstallerUI ( String keyHome, 
			    String keyLib, 
			    String javaHome, 
			    String keyJarPath,			  
			    String os ) {
	super ( keyHome, keyLib, javaHome, keyJarPath, os );
    }

    /**
     * returns true if the given character occurs in the list
     */
    public boolean containsChar ( char c, char[] chars ) {
	
	for ( int i = 0; i < chars.length; i++ ) {
	    if ( chars[i] == c ) {
		return true;
	    }
	}
	
	return false;
    }

    /**
     * Trims String to max. nr chars per line
     */
    public String trim ( String s , int nr ) {
	final char[] ws = new char[] { ';', ' ', ',' };
	StringBuffer result = new StringBuffer ( s );

	int column = 0;
	int fromIndex = 0;
	int brakePosition = -1;

	for ( int i = 0; i < s.length (); i++ ) {
		   
	    if ( s.charAt ( i ) == '\n' ) {
		column = 0;
		brakePosition = -1;
	    } else {
		column++;
	    }

	    if ( containsChar ( s.charAt ( i ), ws ) ) {		
		brakePosition = i;
	    } 

	    if ( column >= nr-1 && brakePosition != -1 ) {
		result.insert ( brakePosition + fromIndex + 1, '\n' );
		fromIndex ++;
		column = 0;
	    }
	}

	return result.toString();
    }
}

