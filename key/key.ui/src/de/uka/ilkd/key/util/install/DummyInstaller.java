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

import java.awt.GraphicsEnvironment;

import javax.swing.JOptionPane;

public class DummyInstaller {

    private DummyInstaller() {}


    public static void main ( String[] args ) {	
	    try {
		if (GraphicsEnvironment.
		    getLocalGraphicsEnvironment().getScreenDevices() == null ||
		    GraphicsEnvironment.
		    getLocalGraphicsEnvironment().getScreenDevices().length==0) {
		}
		JOptionPane.showMessageDialog
		    ( null, 
		      "You must install KeY first. Please run: \n " + 
		      "'java -jar setup.jar'" + 
		      "\n or just double click on 'setup.jar' " + 
		      "(depends on your desktop configuration)",
		      "Installation successfully completed",
		      JOptionPane.INFORMATION_MESSAGE );
		System.exit ( 0 );
	    } catch(Throwable err) {
		System.out.println ( "You must install KeY first. Please run 'java -jar setup.jar'" + 
				     "\n or just double click on 'setup.jar' " + 
				     "(depends on your desktop configuration)" );
	    }
    }

}