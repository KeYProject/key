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

import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
import java.io.File;

import javax.swing.*;
/**
 *   This class creates the GUI element below. The element is used to
 *   enter a path, e.g. where to install or find a program.
 *    -------------------------------------
 *    | text     |======Path======| |...| |
 *    -------------------------------------
 *   The component exists of a leading 'text' followed by a text field
 *   where to enter the path and a button '...'. If it is cliecked on
 *   the button a file choser windows comes up that helps to select
 *   the right directory/file. 
 */
public class InstallationPathChooser extends JPanel {
    
    /**
     * 
     */
    private static final long serialVersionUID = -1310452811820985040L;
    private JButton fileSelectionButton;
    private JTextField pathEntryField;
    private File file;

    /** event listener */
    private InstallationPathListener ipListener = 
	new InstallationPathListener ();
    /** file selection mode */
    private int fileSelectionMode;

    private String label = "";
        
    /** creates an installation path chooser
     * starts with text followed by a textfield
     * @param text a String 
     * @param defaultPath the default path of the file
     * @param mode an int describing the file chooser mode
     */ 
    public InstallationPathChooser ( String text, 
				     String defaultPath,
				     int mode ) {
	this.fileSelectionMode = mode;
	this.file              = new File ( defaultPath );
	this.label             = text;
	setup ( text, defaultPath );
    }

    private void setup ( String text, String defaultPath ) {
	setLayout(new GridLayout(1,1));

	Box slots          = Box.createHorizontalBox();
	JPanel firstSecond = new JPanel(new GridLayout(1,2));

	firstSecond.add ( new JLabel ( text ) );
	pathEntryField = new JTextField ( defaultPath, 15 );
	pathEntryField.addActionListener ( ipListener );
	pathEntryField.addFocusListener  ( ipListener );
	firstSecond.add(pathEntryField);
	slots.add(firstSecond);
	fileSelectionButton=new JButton("...");

	fileSelectionButton.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    if (e.getSource() == fileSelectionButton) {
			JFileChooser chooser=
			    new JFileChooser( pathEntryField.getText () );
			chooser.setFileSelectionMode ( fileSelectionMode );
			int returnVal = chooser.showOpenDialog ( null );
			if ( returnVal == JFileChooser.APPROVE_OPTION ) {
			    pathEntryField.setText
				( chooser.getSelectedFile ().getAbsolutePath () );
			}
		    }
		}
	    });
	slots.add ( fileSelectionButton );
	add ( slots );	
    }
       
    public boolean isFile() {
	return file.isFile();
    }

    public boolean isDirectory() {
	return file.isDirectory();
    }
    

    public String getPath() {
	return file.getPath();
    }

    public String getFile() {
	return isFile() ? file.getName() : "";
    }

    public boolean updateModel () {
	File nf = new File ( pathEntryField.getText () );	
	if ( nf.exists() && 
	     ( fileSelectionMode == JFileChooser.FILES_ONLY && 
	       !nf.isFile () || 
	       ( fileSelectionMode == JFileChooser.DIRECTORIES_ONLY && 
		 !nf.isDirectory () ) ) ) {
	    pathEntryField.selectAll ();
	    return false;
	} else {
	    file = nf;
	    return true;
	}	
    }

    public String setPath ( String path ) {
	String oldPath = pathEntryField.getText();
	pathEntryField.setText ( path );
	return oldPath;
    }

    public void setEnabled(boolean state) {
	pathEntryField.setEnabled ( state );
	fileSelectionButton.setEnabled ( state );
    }

    public String label () {
	return label;
    }

    // static main method
    public static void main(String[] args) {
	JFrame testFrame=new JFrame();
	testFrame.setSize(400,300);
	testFrame.getContentPane().add
	    ( new InstallationPathChooser ( "Install Path", "/home/bubel/", 
					    JFileChooser.FILES_ONLY ) );
	testFrame.setVisible(true);
    }


    // inner listener class
    private class InstallationPathListener 
	implements ActionListener, FocusListener {
	
	public void actionPerformed ( ActionEvent e ) {		    
	    updateModel ();
	}

	public void focusLost ( FocusEvent e ) {		    
	    updateModel ();
	}

	public void focusGained ( FocusEvent e ) {}
    }


}
