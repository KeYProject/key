// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.util.install;

import java.io.PrintWriter;
import java.io.StringWriter;

public class KeYInstallerException extends Exception {

    private Exception e;

    public KeYInstallerException ( String msg ) {
	super ( msg );
    }

    public KeYInstallerException ( String msg, Exception e ) {
	super ( msg );
	this.e = e;
    }

    public String getLocalizedMessage ( ) {
	StringWriter sw = new StringWriter ();
	if (e != null ) {
	    e.printStackTrace ( new PrintWriter ( sw ) );
	}
	return  sw.getBuffer () + super.getLocalizedMessage ();
	
    }

    public String toString () {
	return getLocalizedMessage ();
    }
    
}
