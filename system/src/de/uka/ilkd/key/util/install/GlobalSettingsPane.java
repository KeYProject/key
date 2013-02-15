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

import java.awt.BorderLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;

import javax.swing.*;

/** The installer frame consists of a header, the content pane and a
 * button panel. This content pane is an instance of this class.
 */
public class GlobalSettingsPane extends InstallationPane {

    /**
     * 
     */
    private static final long serialVersionUID = 8493173164648301677L;

    private InstallationPathChooser[] installPath=
	new InstallationPathChooser [ 2 ];

    private String localOs;


    public GlobalSettingsPane ( KeYInstaller installer ) {
	super ( "Global", installer );
	this.localOs = os ();
	setup();
    }
    
    private void setup() {

	setLayout(new BorderLayout());
	Box entries = Box.createVerticalBox();

	// which os
	entries.add 
	    ( createRadioPanel ( "Operating System: ", 
				 supportedOS (),
				 os (), 
				 new ActionListener () {
					 public void actionPerformed ( ActionEvent ae ) {
					     if ( ae.getSource () instanceof JRadioButton ) {
						 localOs = ((JRadioButton)ae.getSource()).getText();
					     }
					 } } ) );
	
	//"Where do you have unpacked KeY.tgz?"	
	installPath [0] = new InstallationPathChooser
	    ( "key.jar", 
	      keyJarFile (), 
	      JFileChooser.FILES_ONLY );
	// "From where do you want to start KeY?"
	installPath [1] = new InstallationPathChooser
	    ( "Installation-Path", 
	      keyHome (), 
	      JFileChooser.DIRECTORIES_ONLY);

        for (InstallationPathChooser anInstallPath : installPath) {
            entries.add(anInstallPath);
        }
	
	add ( entries, BorderLayout.NORTH );
    }

    public JPanel createRadioPanel ( String title,
				     String [] radioDescription,
				     String selected,
				     ActionListener listener ) {

	JPanel radioPanel = new JPanel ( new GridLayout ( 1 ,2 ) );
	radioPanel.add ( new JLabel ( title ) );
	JRadioButton[] box = new JRadioButton [ radioDescription.length ];
	ButtonGroup group = new ButtonGroup ();
	Box radioBox = Box.createHorizontalBox ();
	for ( int i = 0; i < radioDescription.length; i++ ) {

	    box [i] = new JRadioButton ( radioDescription [i], 
					 radioDescription [i].
					 equals ( selected ) );
	    
	    box[i].addActionListener ( listener );
	    group.add ( box [i] );
	    radioBox.add ( box [i] );
	}
	radioPanel.add ( radioBox );

	return radioPanel;
    }
				      

    private boolean checkModel () {
        for (InstallationPathChooser anInstallPath : installPath) {
            if (!anInstallPath.updateModel()) {
                JOptionPane.showMessageDialog
                        (null,
                                "Wrong path for " + anInstallPath.label(),
                                "Wrong Path", JOptionPane.ERROR_MESSAGE);
                return false;
            }
        }
	return true;
    }


    public boolean updateModel () {	

	if ( !checkModel () ) {
	    return false;
	}

	os ( localOs );

	String keyJarPath = path (0);
	File f = new File ( keyJarPath );	

	if ( f.exists() && f.isFile() || 
	     keyJarPath.lastIndexOf ( "key.jar" ) > 0 ) {

	    keyJarPath = f.getParent ();
	    
	    if ( keyJarPath == null ) { // assume current directory
		keyJarPath = ".";
	    }
	}	

	keyJarPath ( keyJarPath );

	keyHome ( path (1) );
	
	return true;
    }

    public String path ( int index ) {
	return installPath [index].getPath ();
    }

}
