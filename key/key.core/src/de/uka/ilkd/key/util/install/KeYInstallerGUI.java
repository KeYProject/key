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

import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.Font;
import java.awt.event.*;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.jar.JarFile;

import javax.swing.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class KeYInstallerGUI extends KeYInstallerUI {


    private final JTabbedPane tabbedPane;
    private final JFrame installerFrame;

    
    public KeYInstallerGUI ( String keyHome, 
			     String keyLib, 
			     String javaHome, 
			     String keyJarPath,			  
			     String os ) {

	super ( keyHome, keyLib, javaHome, keyJarPath, os );	

	installerFrame = new JFrame ( "KeY-Installation Wizard" );
        installerFrame.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);

	tabbedPane = new JTabbedPane();
	installerFrame.getContentPane ().
	    setLayout( new BorderLayout () );
	installerFrame.getContentPane ().
	    add ( tabbedPane, BorderLayout.CENTER );
	installerFrame.getContentPane ().
	    add ( setDefaultButtonPanel(), BorderLayout.SOUTH );

    }

    public void setHeader (JLabel header) {
	installerFrame.getContentPane ().
	    add ( header, BorderLayout.NORTH );
    }

    public void addInstallationPane ( InstallationPane pane ) {
	tabbedPane.addTab ( pane.name (), pane );
    }

    public void setVisible ( boolean b ) {
	installerFrame.setVisible ( b );

    }

    public void requestFocus () {
	installerFrame.requestFocus ();
    }

    public void pack () {
	installerFrame.pack ();
    }

    public void dispose () {
	installerFrame.dispose ();
    }


    public int paneCount () {
	return tabbedPane.getTabCount ();
    }

    public InstallationPane pane ( int index ) {
	return ( InstallationPane ) tabbedPane.getComponentAt ( index );
    }


    protected Container setDefaultButtonPanel() {
	JPanel buttonPanel = new JPanel();
	buttonPanel.setAlignmentX(SwingConstants.CENTER);	
	Box buttonBox = Box.createHorizontalBox();
	
	// create buttons
	JButton prev   = new JButton("<< Back");
	JButton cancel = new JButton("Cancel");
	JButton next   = new JButton("Next >>");
	// add to change listeners
	ChangeListenerWithButton prevListener=new ChangeListenerWithButton(prev) {
	    private void defaultAction() {
		if ( tabbedPane.getSelectedIndex () <= 0 ) {		    
		    button.setEnabled ( false );
		} else {
		    button.setEnabled ( true );
		}
	    }

	    public void stateChanged ( ChangeEvent ce ) {
		defaultAction ();
	    }

	    public void componentAdded ( ContainerEvent e ) {
		defaultAction ();
	    }
	    public void componentRemoved ( ContainerEvent e ) {
		defaultAction ();
	    }		
	};
	tabbedPane.addContainerListener(prevListener);
	tabbedPane.addChangeListener(prevListener); 
	
	ChangeListenerWithButton nextListener = new ChangeListenerWithButton ( next ) {
	    private void defaultAction () {
		if ( tabbedPane.getSelectedIndex() == tabbedPane.getTabCount()-1 ) {		    
			button.setText("Finish");
		} else {
			button.setText("Next >>");
		}
	    }

	    public void stateChanged ( ChangeEvent ce ) {
		defaultAction ();
	    }

	    public void componentAdded ( ContainerEvent e ) {
		defaultAction();
	    }
	    public void componentRemoved ( ContainerEvent e ) {
		defaultAction();
	    }		
	};

	tabbedPane.addContainerListener ( nextListener ); 
	tabbedPane.addChangeListener ( nextListener ); 


	// set action listeners
	prev.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		if ( tabbedPane.getSelectedIndex() > 0 ) {
		    InstallationPane tab = ( InstallationPane ) tabbedPane.
			getSelectedComponent();
		    if ( tab.updateModel () ) {
			tabbedPane.setSelectedIndex 
			    ( tabbedPane.getSelectedIndex() - 1 );
		    }			
		}
	    }
	});
	
	cancel.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		cancelled();
	    }
	});

	next.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		InstallationPane tab = ( InstallationPane ) tabbedPane.
		    getSelectedComponent();
		if ( tab.updateModel () ) {
		    if (tabbedPane.getSelectedIndex()<tabbedPane.getTabCount()-1) {
			    tabbedPane.setSelectedIndex 
			        ( tabbedPane.getSelectedIndex() + 1 );
		    } else {
                        try {
                            installerFrame.setCursor(new java.awt.Cursor(
                                java.awt.Cursor.WAIT_CURSOR));
                            finish();
                            if (complete()) System.exit(0);
                        } catch(NotCompleteException nce) {
                            // let the user take care of it
                        } finally {
                            installerFrame.setCursor(new java.awt.Cursor(
                                java.awt.Cursor.DEFAULT_CURSOR));
                        }
                    }
                }
	    }
	});
	
	// disable the tabbed pane in order to prevent the user from 
	// circumventing the consistency checking and model updating 
	// done by the "next" button 
	tabbedPane.setEnabled(false);
	
	// add buttons
	buttonBox.add(prev);
	buttonBox.add(cancel);
	buttonBox.add(next);
	buttonPanel.add(buttonBox);
	return buttonPanel;
     }

    private void cancelled() {
	JOptionPane.showMessageDialog
	    ( null, "Installation cancelled.",
	      "Installation cancelled",
	      JOptionPane.INFORMATION_MESSAGE );
	System.exit (-1);
    }

    private boolean complete() {

	if ( ! updateModel() ) {
	    return false;
	}

	File jarFile = new File ( keyJarFile () );

	if ( !jarFile.exists () ) {
	    JOptionPane.showMessageDialog 
		( null, 
		  trim ( "Could not find 'key.jar' in " + keyJarPath () + 
			 ". Please enter the correct part in section " + 
			 "'Global Settings | key.jar'", 60 ),
		  "File Missing", JOptionPane.ERROR_MESSAGE );
	    return false;
	}

	String [] missingLibs; 
	int option = 2;
	
	missingLibs = checkLibraries ();
	do {
	    if ( missingLibs.length > 0 ) {
		Object[] options = { "Continue anyway", 
				     "Go back", 
				     "Check again" };
		option = JOptionPane.showOptionDialog 
		    ( null, 
		      trim ( "Please copy the external libraries to " + 
			     keyLib () + ". You can download them from: " + 
			     "http://www.key-project.org/download/", 
			     60 ), "Libraries Missing", 
		      JOptionPane.DEFAULT_OPTION, 
		      JOptionPane.WARNING_MESSAGE,
		      null, options, options [option] );	  
	    } 
	    missingLibs = checkLibraries ();
	} while ( missingLibs.length > 0 && option == 2 ); 
		
	return option != 1;
    }

    private void abortError( String err ) {
        JOptionPane.showMessageDialog 
	    ( null, 
	      trim ( "Installation cannot proceed due to an error:\n" + 
		     err, 60 ),
	      "Installation Not Finished",
	      JOptionPane.ERROR_MESSAGE );
        throw new NotCompleteException();  		    
// 	    System.exit ( -1 );
    }
    
    private static class NotCompleteException extends RuntimeException {

        /**
         * 
         */
        private static final long serialVersionUID = 5345835460812915864L;
    }
    

    private boolean updateModel() {
	for ( int i = 0; i < tabbedPane.getTabCount (); i++ ) {
	    if ( tabbedPane.getComponentAt ( i ) instanceof InstallationPane ) {
		if ( ! ( ( InstallationPane ) tabbedPane.getComponentAt ( i ) ).updateModel () ) {
		    tabbedPane.setSelectedIndex ( i );
		    return false;
		}
	    }
	}
	return true;
    }
    
    private void finish() {

	StringBuffer todo = new StringBuffer ( "" );

	File keyJar = new File ( keyJarFile () );
	JarFile keyJarFile = null;

	try {
	    keyJarFile = new JarFile ( new File ( keyJarFile () ) );
	} catch ( FileNotFoundException fne ) {	    
	    abortError ( "Did not find a valid jar file at " + keyJarPath () + 
			 " Please check its existence and " + 
			 "its read and write access permissions.\nDetail: " + fne );
	} catch ( IOException ioe ) {
	    abortError ( "Error when trying to access 'key.jar' at " + keyJarPath () + 
			 ".\nDetail: " + ioe );	    
	}
	String [] missingLibs = new String [0];

	mkdirs ();	

	missingLibs = checkLibraries ();
       	

	try {
	    generateScripts ( keyJarFile );
	} catch ( KeYInstallerException kie ) {
 	    abortError ( "Could not generate the shell scripts. Please " + 
 		    "resolve the problem first " + 
 		    "and redo the installation afterwards.\nDetail: " + kie );
 	}

	File examplesFile = new File(keyJarPath(), EXAMPLES_JAR_FILE);
	try {
		JarFile examplesJarFile = new JarFile(examplesFile);
		extractExamples( examplesJarFile );
 	} catch (IOException e) {
 		abortError ( "Could not unpack the examples. Please " + 
 				"resolve the problem first " + 
 				"and redo the installation afterwards.\nDetail:" + e );	    
        }
	
	if ( "linux".equals ( os () ) ) {
	    try {
		Runtime.getRuntime ().exec ( new String[]{"chmod", "a+x", startProverScriptFilePath ()});
	    } catch ( IOException e) { 
		todo.append ( "Please set " + startProverScriptFilePath () +  
			      " executable : chmod a+x " + startProverScriptFilePath ());
		todo.append ( "\n" );
	    }
	}

	try {
	    copy( keyJar, systemPath () );
	} catch ( KeYInstallerException kie ) {
	    todo.append ( " Copy file 'key.jar' from " + keyJar + 
			  " to " + systemPath () + 
			  "\n\t usually this should be done automatically, " + 
			  "but failed due to: " + kie );
	    todo.append ( "\n" );
	}

	if ( missingLibs.length > 0 ) {
	    todo.append ( "Please copy the following libraries to " );
	    todo.append ( keyLib () );
	    for ( int i = 0; i < missingLibs.length; i++ ) {
		todo.append ( "\n" );
		todo.append ( i + ". " + missingLibs [i] );
	    }
	    todo.append ( "\n" );
	} 
   

	if ( todo.length () > 0 ) {
	    JOptionPane.showMessageDialog 
		( null, 
		  trim (  "Something is left to do. " + todo.toString () + 
			  "After you have done all from above, you can start KeY by" + 
			  " changing to " + binaryPath () + 
			  " and executing " + startProverScriptFileName (), 60 ),
			  "Please complete installation manually", 
		  JOptionPane.INFORMATION_MESSAGE );
	} else {
	    JOptionPane.showMessageDialog
		( null, trim 
		  ( "To start KeY, change directory to "
		    + binaryPath () +  " and execute " + 
		    startProverScriptFileName () +
		    ". Examples can be found using 'Load " +
		    "Examples' from the 'File' menu.", 60 ),
		  "Installation successfully completed",
		  JOptionPane.INFORMATION_MESSAGE );
	}
    }
       
    public void start () {	

	JLabel header = new JLabel();

	header.setFont(new Font("Header Font", Font.PLAIN, 24));
	header.setText("KeY-Installer");
	header.setIcon ( de.uka.ilkd.key.gui.IconFactory.keyLogo (50, 40) );
	header.setHorizontalAlignment(SwingConstants.CENTER);

	setHeader(header);
	addInstallationPane ( new WelcomePane ( this ) );
	addInstallationPane ( new GlobalSettingsPane ( this ) );
	addInstallationPane ( new LibrarySettingsPane ( this ) );

	pack ();
	setVisible ( true );
	
    }


    // Change listener for tabbed pane
    abstract static class ChangeListenerWithButton 
	implements ChangeListener, ContainerListener {

	protected JButton button;

	public ChangeListenerWithButton(JButton button) {
	    this.button = button;
	}

	public abstract void stateChanged(ChangeEvent ce);

	public abstract void componentAdded(ContainerEvent e);
	public abstract void componentRemoved(ContainerEvent e);
  

    }




}