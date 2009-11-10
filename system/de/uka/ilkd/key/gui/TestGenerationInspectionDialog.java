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
            msgScroll.setPreferredSize(new java.awt.Dimension(500, 500));
        getContentPane().add(msgScroll);

        
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

}
