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

import javax.swing.JPanel;
/** The installer frame consists of a header, the content pane and a
 * button panel. This content pane is an instance of this class.
 */

public abstract class InstallationPane extends JPanel {

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

    public String togetherHome () {
	return installer.togetherHome ();
    }


    public void keyHome ( String dir ) {
	installer.keyHome ( dir );
    }

    public void keyLib ( String dir ) {
	installer.keyLib ( dir );
    }

    public void togetherHome ( String dir ) {
	installer.togetherHome ( dir );
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
     * returns directory of Together version
     */
    public String togetherVersion () {
	return installer.togetherVersion ();
    }

    /**
     * returns list of all supported together version
     */
    public String[] supportedTgVersion () {
	return installer.supportedTgVersion ();
    }

    /**
     * sets version of together 
     */
    public void togetherVersion ( String vers ) {
	installer.togetherVersion ( vers );
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
