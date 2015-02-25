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

import javax.swing.JPanel;
/** The installer frame consists of a header, the content pane and a
 * button panel. This content pane is an instance of this class.
 */

public abstract class InstallationPane extends JPanel {

    /**
     * 
     */
    private static final long serialVersionUID = -5956711910075180613L;
    private String name;
    private KeYInstaller installer;

    public InstallationPane ( String name,
			      KeYInstaller installer ) {
	this.name = name;
	this.installer = installer;
	setRequestFocusEnabled ( true );
    }

    public String keyHome () {
	return installer.keyHome ();
    }

    public String keyLib () {
	return installer.keyLib ();
    }

    public void keyHome ( String dir ) {
	installer.keyHome ( dir );
    }

    public void keyLib ( String dir ) {
	installer.keyLib ( dir );
    }

    /**
     * returns path where to find key.jar 
     */
    public String keyJarPath () {
	return installer.keyJarPath ();
    }

    /**
     * returns complete path to find key.jar 
     */
    public String keyJarFile () {
	return installer.keyJarFile ();
    }

    public String[] supportedOS () {
	return installer.supportedOS ();
    }

    public String os () {
	return installer.os ();
    }

    public void os ( String os ) {
	installer.os ( os );
    }

    /**
     * sets path where to find key.jar 
     */
    public void keyJarPath ( String dir ) {
	installer.keyJarPath ( dir );
    }
    
    public abstract boolean updateModel ();

    public String name () {
	return name;
    }

}