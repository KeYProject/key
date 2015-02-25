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

package de.uka.ilkd.key.util.install;

import java.io.PrintWriter;
import java.io.StringWriter;

public class KeYInstallerException extends Exception {

    /**
     * 
     */
    private static final long serialVersionUID = 4811766923178331697L;
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