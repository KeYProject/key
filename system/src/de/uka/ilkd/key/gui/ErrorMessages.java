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

package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.ByteArrayOutputStream;

import javax.swing.*;

public class ErrorMessages {

    private ErrorMessages() {}

    public static void showBugMessage(Frame owner,String s, Exception e) {
	showBugHelp(new JDialog(owner, "Internal error", true), s, e);
    }

    public static void showBugMessage(Dialog owner,String s, Exception e) {
	showBugHelp(new JDialog(owner, "Internal error", true), s, e);
    }
 
    private static void showBugHelp(JDialog f, String s, Exception e) {
	JPanel p = new JPanel();
	p.setLayout(new BorderLayout());
	p.setBorder(new javax.swing.border.TitledBorder(""));
	JPanel mp= new JPanel();
	mp.setLayout(new BoxLayout(mp, BoxLayout.Y_AXIS));
	mp.add(new JLabel("An internal error in the KeY system occurred."));
	mp.add(new JLabel(">>"+s+"<<" ));
	mp.add(new JLabel());
	mp.add(new JLabel("Please, report this error to the KeY team"));
	mp.add(new JLabel("by describing what you did and by submitting"));
	mp.add(new JLabel("the complete stack trace from below."));
	mp.add(new JLabel("If you have access, please use the KeY Bugtracker at"));
	mp.add(new JLabel("http://i12www.ira.uka.de/~klebanov/mantis"));
	p.add(mp, BorderLayout.NORTH);
	ByteArrayOutputStream byteOut=new ByteArrayOutputStream();
	java.io.PrintStream out=new java.io.PrintStream(byteOut);
	e.printStackTrace(out);
	JTextArea stack=new JTextArea(">>"+s+"<<\n"+byteOut.toString(),10,30);
	JScrollPane scroll=new JScrollPane();
	scroll.setViewportView(stack);
	stack.setEditable(false);
	p.add(scroll, BorderLayout.CENTER);

	JPanel bp=new JPanel(new GridBagLayout());
	GridBagConstraints c = new GridBagConstraints();

	ActionListener dlgCloseListener = new ActionListener(){
		public void actionPerformed(ActionEvent ae){
		    Component cm=(Component)ae.getSource();
		    while (!(cm instanceof Window)) {
			cm=cm.getParent();
		    }
		    cm.setVisible(false);
		    ((Window)cm).dispose();
		}
	    };
	JButton okb=new JButton("Done");
	okb.addActionListener(dlgCloseListener);
	c.insets = new Insets(5,20,5,20);
	c.gridx = 0;
	bp.add(okb, c);    
	bp.setAlignmentY(Component.BOTTOM_ALIGNMENT);
	p.add(bp, BorderLayout.SOUTH);
	f.getContentPane().add(p);
	f.pack();
	f.setVisible(true);
    }

    public static void handleExceptionType(Frame owner, String s, 
					   Exception e) {
	if (e instanceof NullPointerException || e instanceof ClassCastException) {
	    showBugMessage(owner, s, e);
	}
    }


}