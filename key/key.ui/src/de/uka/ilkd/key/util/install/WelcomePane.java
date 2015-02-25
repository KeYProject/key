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

import java.awt.Font;
import java.awt.GridLayout;

import javax.swing.JTextArea;
import javax.swing.SwingConstants;

/** The installer frame consists of a header, the content pane and a
 * button panel. This content pane is an instance of this class.
 */
public class WelcomePane extends InstallationPane {

    /**
     * 
     */
    private static final long serialVersionUID = 6205049648488646558L;


    public WelcomePane ( KeYInstaller installer ) {

	super ( "Welcome", installer );

	setLayout ( new GridLayout ( 1, 1 ) );
	JTextArea text=new JTextArea ( 5, 30 );
	text.setLineWrap ( true );
	text.setAlignmentX ( SwingConstants.CENTER );
	text.setFont ( new Font( "Header Font", Font.PLAIN, 14 ) );
	text.setWrapStyleWord ( true );
	text.setText 
	    ( "Dear User,\n"+
	      "   thank you for choosing KeY. In case of any questions, problems " +
	      "or suggestions please contact us: support@key-project.org\n" +  
	      "We would also be interested to know for which purpose you " + 
	      "will use KeY, e.g. research, industry or teaching.\n" + 
	      "\t Best regards,\n" +
	      "\t    Your KeY-Team" );
	text.setEditable ( false );
	text.setBackground ( getBackground () );
	add ( text );
    }


    public boolean updateModel () {	
	return true;
    }

}