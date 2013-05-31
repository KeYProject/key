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

import javax.swing.Box;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.JTextArea;

/** The installer frame consists of a header, the content pane and a
 * button panel. This content pane is an instance of this class.
 */
public class LibrarySettingsPane extends InstallationPane {

    /**
     * 
     */
    private static final long serialVersionUID = 961855442417412207L;
    private InstallationPathChooser chooser = null;

    public LibrarySettingsPane ( KeYInstaller installer ) {
	super ( "Library", installer );
	setup ();
    }
    
    private void setup () {
	setLayout ( new BorderLayout () );       
	Box box = Box.createVerticalBox ();
	
	JTextArea text = new JTextArea ( 5, 30 );
	text.setLineWrap ( true );
	text.setWrapStyleWord ( true );
	text.setText ( "KeY makes use of several external libraries. " +
		       "You can download them from the KeY-Homepage: " +
		       "http://www.key-project.org/download/3rdparty.html\n"+
		       "Please make sure that all required libraries are "+
		       "located in the indicated library path." );
	text.setEditable ( false );
	text.setBackground ( getBackground () );
	box.add ( text );

	chooser = new InstallationPathChooser
	    ( "Library Path", keyLib (), JFileChooser.DIRECTORIES_ONLY );
	box.add ( chooser );	

	add ( box, BorderLayout.NORTH );
    }

    public String path ( ) {
	return chooser.getPath();
    }

    public String path ( String path ) {
	return chooser.setPath ( path );
    }

    public boolean updateModel () {	
	if ( ! chooser.updateModel () ) {
	    JOptionPane.showMessageDialog 
		( null, 
		  "Library is not a directory.",
		  "Wrong Library Directory", JOptionPane.ERROR_MESSAGE );
	    return false;	    
	}
	keyLib ( path () );
	return true;
    }


}
