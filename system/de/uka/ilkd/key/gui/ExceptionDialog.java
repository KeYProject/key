// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.Dialog;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.io.PrintWriter;
import java.io.StringWriter;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.SVInstantiationExceptionWithPosition;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.ExtList;

public class ExceptionDialog extends JDialog {

    private JPanel buttonPanel; 
    private JScrollPane listScroll,stScroll;    
    private StringWriter sw;
    private PrintWriter pw;
    private Object[] exceptionArray;
    private JTextArea stTextArea;
    private boolean withList = false;

    private Location getLocation(Object exc){
	Location location=null;
	if  (exc instanceof antlr.RecognitionException) { 
	    location = new Location(((antlr.RecognitionException)exc).getFilename(),
				    ((antlr.RecognitionException) exc).getLine(),
				    ((antlr.RecognitionException) exc).getColumn());
	} else if (exc instanceof ParserException) {
	       location = ((ParserException) exc).getLocation();
        } else if (exc instanceof SLTranslationException) {
            SLTranslationException ste = (SLTranslationException) exc;
            location = new Location(ste.getFileName(), 
                                    ste.getLine(), 
                                    ste.getColumn());
        } else if (exc instanceof RuntimeException 
                   && ((RuntimeException) exc).getCause() 
                       instanceof SLTranslationException) {
            SLTranslationException ste 
                = (SLTranslationException) ((RuntimeException) exc).getCause();
            location = new Location(ste.getFileName(),
                                    ste.getLine(),
                                    ste.getColumn());
	} else if (exc instanceof SVInstantiationExceptionWithPosition) {	      
		location = new Location(null, 
			       ((SVInstantiationExceptionWithPosition)exc).getRow(),
	         	       ((SVInstantiationExceptionWithPosition)exc).getColumn());
	}
	return location;
    }


    private JPanel createButtonPanel(){
	 JButton closeButton = new JButton( "Close" );
         JCheckBox detailsBox  = new JCheckBox("Show Details");
         detailsBox.setSelected(false);
	 JPanel bPanel = new JPanel();
	 bPanel.add(closeButton);
	 bPanel.add(detailsBox);

	 ActionListener closeListener = new ActionListener() {
		 public void actionPerformed( ActionEvent e ) {
		     setVisible(false);
                     dispose();
		 }
	 };

	 ItemListener detailsBoxListener = new ItemListener() {
		 public void itemStateChanged(ItemEvent e) {
		     if (e.getStateChange() == ItemEvent.SELECTED){
			 if (withList) getContentPane().add(listScroll); 
			 getContentPane().add(stScroll); 
		     } else {
			 if (withList) getContentPane().remove(listScroll);
			 getContentPane().remove(stScroll); 
		     }
                     pack();
		     setLocationRelativeTo(null);
		     getContentPane().repaint();
     		 }
	 };
	 closeButton.addActionListener(closeListener);
	 detailsBox.addItemListener(detailsBoxListener);
	 return bPanel;
    }
    

    private JScrollPane createJListScroll(Object[] excArray){
	 String[] excMessages = new String[excArray.length];
	 for (int i= 0; i<excArray.length;i++){
	     if (!(getLocation(exceptionArray[i])==null))
	     excMessages[i] = (i+1)+".) Location: " +  getLocation(excArray[i]) + "\n"+
	     (((Throwable)excArray[i]).getMessage());	 	
	     else excMessages[i] = (i+1)+".) " +
	     (((Throwable)excArray[i]).getMessage());
	 }
	 final JList list = new JList(excMessages);
	 list.setCellRenderer( new TextAreaRenderer() );
 	 list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
	 list.setSelectedIndex(0);
	 JScrollPane elistScroll = 
	     new JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, 
	             JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
	 elistScroll.getViewport().setView(list);
	 elistScroll.setBorder(new TitledBorder("Exceptions/Errors"));
	 Dimension paneDim = new Dimension(500, 100);
	 elistScroll.setPreferredSize(paneDim);
	 ListSelectionListener listListener = new ListSelectionListener() {
		 public void valueChanged(ListSelectionEvent e) {
		     	sw = new StringWriter();
			pw = new PrintWriter(sw);
			((Throwable) exceptionArray[list.getSelectedIndex()]).printStackTrace(pw);
			stTextArea.setText
			    ( "("+exceptionArray[list.getSelectedIndex()].getClass()+
			      ") \n"+sw.toString());
		 }
	 };
         list.addListSelectionListener(listListener);
	 return elistScroll;

    }


    private JScrollPane createTextAreaScroll(Object[] excArray) {
	     stTextArea = new JTextArea();
	     stTextArea.setEditable(false);
	     Dimension textPaneDim = new Dimension(500, 300);
	     JScrollPane Scroll = new JScrollPane(stTextArea);
	     Scroll.setBorder(new TitledBorder("Stack Trace"));
	     Scroll.setPreferredSize(textPaneDim);
 	     sw = new StringWriter();
	     pw = new PrintWriter(sw);
	     ((Throwable) excArray[0]).printStackTrace(pw);
	     stTextArea.setText("("+excArray[0].getClass()+
			      ") \n"+sw.toString());
	     return Scroll;
    }

    private JScrollPane createExcTextAreaScroll(Object[] excArray) {
	     JTextArea exTextArea = new JTextArea();
	     exTextArea.setEditable(false);
	     Dimension textPaneDim = new Dimension(500, 100);
	     exTextArea.setColumns(120);
	     exTextArea.setLineWrap(true);
	     exTextArea.setWrapStyleWord(true);	 
	     JScrollPane Scroll = new JScrollPane(exTextArea);
	     Scroll.setBorder(new TitledBorder(""+excArray[0].getClass()));
	          Scroll.setPreferredSize(textPaneDim);
	     exTextArea.setText(((Throwable) excArray[0]).getMessage());            
	     return Scroll;
    }


    private JPanel createLocationPanel(Object[] excArray){
	Location loc = getLocation(excArray[0]);
	JPanel lPanel = new JPanel();
	JTextField fTextField,lTextField, cTextField;
	fTextField = new JTextField();
	lTextField = new JTextField();
	cTextField = new JTextField();
	fTextField.setEditable(false);
	lTextField.setEditable(false);
	cTextField.setEditable(false);
	if (!(loc==null)) {
	    if ( !( (loc.getFilename()==null) || (loc.getFilename()== ""))){
		fTextField.setText("File: "+loc.getFilename());
		lPanel.add(fTextField);
	    } 
	    if (excArray[0] instanceof SVInstantiationExceptionWithPosition)
		lTextField.setText("Row: "+ +loc.getLine());
	    else lTextField.setText("Line: "+loc.getLine());
	    lPanel.add(lTextField);
	    cTextField.setText("Column: "+loc.getColumn());
  	    lPanel.add(cTextField);
	}
	return lPanel;
    }


    public ExceptionDialog(Dialog parent, ExtList excList) {
        super(parent, "Parser Messages", true); 
        init(excList);
   }

    public ExceptionDialog(Dialog parent, Exception exc) {
        super(parent, "Parser Messages", true); 
        ExtList msgList = new ExtList();
        msgList.add(exc);
        init(msgList);
   }

    public ExceptionDialog(JFrame parent, ExtList excList) {
        super(parent, "Parser Messages", true);   
        init(excList);
    }
    
    public ExceptionDialog(JFrame parent, Exception exc) {
        super(parent, "Parser Messages", true);   
        ExtList msgList = new ExtList();
        msgList.add(exc);
        init(msgList);
    }


    private void init(ExtList excList) {
        buttonPanel = createButtonPanel();
        if (excList.size()!=0) {
         if (excList.size()>1) withList=true;
            exceptionArray = excList.toArray();
            getContentPane().setLayout(new BoxLayout(getContentPane(), 
                    BoxLayout.Y_AXIS));
            stScroll = createTextAreaScroll(exceptionArray);
            listScroll = createJListScroll(exceptionArray);
            getContentPane().add(createExcTextAreaScroll(exceptionArray));
            getContentPane().add(createLocationPanel(exceptionArray));
            getContentPane().add(buttonPanel);
            setDefaultCloseOperation(DISPOSE_ON_CLOSE);
            pack();
            setLocationRelativeTo(null);
            setVisible(true);
        } else {
            dispose();
        }
    }


    class TextAreaRenderer extends JTextArea implements ListCellRenderer
    {
        public TextAreaRenderer()
        {	   
            setLineWrap(true);
	    setWrapStyleWord(true);
	    setRows(3);
        }
                      
        
        public Component getListCellRendererComponent(JList list, Object value,
            int index, boolean isSelected, boolean cellHasFocus)
        {                                     
            if (index==0) setFont(getFont().deriveFont(Font.BOLD, 12)); 
	    else setFont(getFont().deriveFont(Font.PLAIN, 12)); 
            setText(value.toString());
            setBackground(isSelected ? list.getSelectionBackground() : null);
            setForeground(isSelected ? list.getSelectionForeground() : null);                                             
            return new JScrollPane(this);
        }
    }

}
