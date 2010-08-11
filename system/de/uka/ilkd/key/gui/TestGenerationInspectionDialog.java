// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui;


import java.awt.Dimension;
import java.awt.event.WindowEvent;
import java.awt.event.WindowStateListener;

import javax.swing.BoxLayout;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;

public class TestGenerationInspectionDialog extends JDialog {
    
    static TestGenerationInspectionDialog dialog;
    public static JTextArea msg = new JTextArea(); 
    public static JTextArea createModelsHelp = new JTextArea(); 
    
    /**When invoked the first time, the parent must be set. In subsequent calls
     * parent may be null. */
    public static TestGenerationInspectionDialog getInstance(JFrame parent){
	if(dialog==null){
	    dialog = new TestGenerationInspectionDialog(parent);	    
	}
	dialog.pack();
	return dialog;
    }
    public TestGenerationInspectionDialog(JFrame parent){
	super(parent, "Test Generation Inspection Dialog");
	getContentPane().setLayout(new BoxLayout(getContentPane(),BoxLayout.Y_AXIS));
		
		msg.setAutoscrolls(true);
                JScrollPane msgScroll = new
                JScrollPane(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, 
                        ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            msgScroll.getViewport().setView(msg);
            msgScroll.setBorder(new TitledBorder("Messages"));
            msgScroll.setPreferredSize(new java.awt.Dimension(700, 600));
        getContentPane().add(msgScroll);
        
            createModelsHelp.setPreferredSize(new java.awt.Dimension(700, 100));
            //createModelsHelp.setAutoscrolls(true);
        getContentPane().add(createModelsHelp);

        
	this.addWindowStateListener(new WindowStateListener(){
	    public void windowStateChanged(WindowEvent arg0) {
	        // TODO Auto-generated method stub
	        if(arg0.getNewState()==WindowEvent.WINDOW_CLOSED){
	            msg.setText("");
	        }
            }
	});
    }
    
    public void msg(String txt){
	if(txt!=null)
	    msg.append(txt+"\n");
    }
    
    public void createModelsHelpMsg(String txt){
	if(txt!=null)
	    createModelsHelp.setText(txt);
    }

}
