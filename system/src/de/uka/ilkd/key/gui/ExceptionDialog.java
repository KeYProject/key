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

package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.Container;
import java.awt.Dialog;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Frame;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Arrays;
import java.util.List;
import java.util.Vector;

import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.ListCellRenderer;
import javax.swing.ListSelectionModel;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.parser.KeYSemanticException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.parser.proofjava.Token;
import de.uka.ilkd.key.proof.SVInstantiationExceptionWithPosition;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * Dialog to display error messages.
 * 
 * @author refactored by mattias
 */
public class ExceptionDialog extends JDialog {

    /**
     * 
     */
    private static final long serialVersionUID = -4532724315711726522L;
    private JScrollPane listScroll, stScroll;    
    private boolean withList = false;
    private JTextArea stTextArea;
    
    public static void showDialog(Dialog parent, Throwable exception) {
        showDialog(parent, Arrays.asList(exception));
    }
    
    public static void showDialog(Frame parent, List<Throwable> excList) {
        if (excList.size() != 0) {
            ExceptionDialog dlg = new ExceptionDialog(parent, excList);
            dlg.setVisible(true);
            dlg.dispose();
        }
    }
    
    public static void showDialog(Frame parent, Throwable exception) {
        showDialog(parent, Arrays.asList(exception));
    }

    private ExceptionDialog(Dialog parent, List<Throwable> excList) {
        super(parent, "Parser Messages", true); 
        init(excList);
    }

    private ExceptionDialog(Frame parent, List<Throwable> excList) {
        super(parent, "Parser Messages", true);   
        init(excList);
    }

    // result may be null
    private Location getLocation(Throwable exc) {
        assert exc != null;

	Location location = null;

	if  (exc instanceof antlr.RecognitionException) { 
	    location = new Location(((antlr.RecognitionException)exc).getFilename(),
				    ((antlr.RecognitionException) exc).getLine(),
				    ((antlr.RecognitionException) exc).getColumn());
        }
        if  (exc instanceof org.antlr.runtime.RecognitionException) {
            // ANTLR 3 - Recognition Exception.
            String filename = "";
            if(exc instanceof KeYSemanticException) {
                filename = ((KeYSemanticException)exc).getFilename();
            }

            org.antlr.runtime.RecognitionException recEx =
                    (org.antlr.runtime.RecognitionException) exc;
            location = new Location(filename, recEx.line, recEx.charPositionInLine);
        }
	else if (exc instanceof ParserException) {
	    location = ((ParserException) exc).getLocation();
	} else if (exc instanceof ParseException) {
	    ParseException pexc = (ParseException)exc;
	    Token token = pexc.currentToken;
	    // TODO find out filename here
	    location = token==null? null: new Location("", token.next.beginLine, token.next.beginColumn);
        } else if (exc instanceof SLTranslationException) {
            SLTranslationException ste = (SLTranslationException) exc;
            location = new Location(ste.getFileName(), 
                                    ste.getLine(), 
                                    ste.getColumn());
        } else if (exc instanceof SVInstantiationExceptionWithPosition) {	      
            location = new Location(null, 
			       ((SVInstantiationExceptionWithPosition)exc).getRow(),
	         	       ((SVInstantiationExceptionWithPosition)exc).getColumn());
	} 

	if (location == null && exc.getCause() != null) {
	    location = getLocation(exc.getCause());
	}

	return location;
    }


    private JPanel createButtonPanel() {
        ActionListener closeListener = new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
            }
        };
        
        ItemListener detailsBoxListener = new ItemListener() {
            public void itemStateChanged(ItemEvent e) {
                Container contentPane = getContentPane();
                if (e.getStateChange() == ItemEvent.SELECTED){
                    contentPane.add(stScroll, new GridBagConstraints(0, 3, 1, 1, 1., 10.,
                            GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(
                                    0, 0, 0, 0), 0, 0)); 
                } else {
                    contentPane.remove(stScroll); 
                }
                pack();
                // setLocationRelativeTo(null);
                contentPane.repaint();
            }
        };

//        JButton reloadButton = new JButton("Reload");
//        reloadButton.setAction(MainWindow.getInstance().getOpenMostRecentFileAction());      
//        reloadButton.addActionListener(closeListener);
        
        JButton closeButton = new JButton("Close");
        closeButton.addActionListener(closeListener);
        getRootPane().setDefaultButton(closeButton);
        
        JCheckBox detailsBox  = new JCheckBox("Show Details");
        detailsBox.setSelected(false);
        detailsBox.addItemListener(detailsBoxListener);

        JPanel bPanel = new JPanel();
//        bPanel.add(reloadButton); // XXX useful for debugging
        bPanel.add(closeButton);
        bPanel.add(detailsBox);
        
        return bPanel;
    }
    

    private JScrollPane createJListScroll(final List<Throwable> exceptions) {
	 Vector<String> excMessages = new Vector<String>();
	 int i = 1;
	 for (Throwable throwable : exceptions) {
            Location location = getLocation(throwable);
            if(location != null) {
                excMessages.add(i + ") Location: " +  location + "\n" + throwable.getMessage());
            } else {
                excMessages.add(i + ") " + throwable.getMessage());
            }
            i ++;
	 }
	 
	 final JList list = new JList(excMessages);
	 list.setCellRenderer(new TextAreaRenderer());
 	 list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
	 list.setSelectedIndex(0);
	 
	 JScrollPane elistScroll = 
	     new JScrollPane(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, 
	             ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
	 elistScroll.getViewport().setView(list);
	 elistScroll.setBorder(new TitledBorder("Exceptions/Errors"));
	 elistScroll.setPreferredSize(new Dimension(500, 300));

	 ListSelectionListener listListener = new ListSelectionListener() {
	     public void valueChanged(ListSelectionEvent e) {
	         Throwable exc = exceptions.get(list.getSelectedIndex());
	         setStackTraceText(exc);
	     }
	 };
	 
         list.addListSelectionListener(listListener);
	 return elistScroll;

    }
    
    private JScrollPane createStacktraceTextAreaScroll() {
        JScrollPane scroll = new JScrollPane(stTextArea);
        scroll.setBorder(new TitledBorder("Stack Trace"));
        scroll.setPreferredSize(new Dimension(500, 300));
        return scroll;
    }


    private JTextArea createStacktraceTextArea() {
        JTextArea result = new JTextArea();
        result.setEditable(false);
        return result;
    }
    
    private void setStackTraceText(Throwable exc) {
        StringWriter sw = new StringWriter();
        sw.append("(" + exc.getClass() + ")\n");
        PrintWriter pw = new PrintWriter(sw);
        exc.printStackTrace(pw);
        stTextArea.setText(sw.toString());
    }

    private JScrollPane createExcTextAreaScroll(List<Throwable> excArray) {
        Throwable exc = excArray.get(0);
        JTextArea exTextArea = createStacktraceTextArea();
        Dimension textPaneDim = new Dimension(500, 200);
        exTextArea.setColumns(120);
        exTextArea.setLineWrap(true);
        exTextArea.setWrapStyleWord(true);
        exTextArea.setText(exc.getMessage());	     

        exTextArea.setTabSize(2);

        // ensures that the dialog shows the error messaged scrolled to its start
        exTextArea.setCaretPosition(0);

        JScrollPane scroll = new JScrollPane(exTextArea);
        scroll.setBorder(new TitledBorder(exc.getClass().getName()));
        scroll.setPreferredSize(textPaneDim);

        return scroll;
    }

    // returns null if no location can be extracted.
    private JPanel createLocationPanel(List<Throwable> excArray) {
	Throwable exc = excArray.get(0);
	Location loc = getLocation(exc);
	
	if (loc == null) {
	    return null;
	}
	
	JPanel lPanel = new JPanel();
	JTextField fTextField, lTextField, cTextField;
	fTextField = new JTextField();
	lTextField = new JTextField();
	cTextField = new JTextField();
	fTextField.setEditable(false);
	lTextField.setEditable(false);
	cTextField.setEditable(false);
	
	
	if ( !( loc.getFilename()==null || "".equals(loc.getFilename()))) {
	    fTextField.setText("File: " + loc.getFilename());
	    lPanel.add(fTextField);
	} 

	if (exc instanceof SVInstantiationExceptionWithPosition) {
	    lTextField.setText("Row: " + loc.getLine());
	} else { 
	    lTextField.setText("Line: " + loc.getLine());
	}
	
	lPanel.add(lTextField);

	cTextField.setText("Column: " + loc.getColumn());
	lPanel.add(cTextField);
	
	return lPanel;
    }

    public static void showDialog(Dialog parent, List<Throwable> excList) {
        if (excList.size() != 0) {
            ExceptionDialog dlg = new ExceptionDialog(parent, excList);
            dlg.setVisible(true);
            dlg.dispose();
        }
    }
    
    private void init(List<Throwable> excList) {
        withList = (excList.size() > 1);
        
        Container cp = getContentPane();
        cp.setLayout(new GridBagLayout());
        
        listScroll = createJListScroll(excList);
        
        if(withList) {
            cp.add(listScroll, new GridBagConstraints(0, 0, 1, 1, 1., 1.,
                    GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(
                            0, 0, 0, 0), 0, 0));
        } else {
            cp.add(createExcTextAreaScroll(excList), 
                    new GridBagConstraints(0, 0, 1, 1, 1., 1e-10,
                    GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(
                            0, 0, 0, 0), 0, 0));
        }
            
        JPanel locationPanel = createLocationPanel(excList);
        // currently no locations with lists
        if(!withList && locationPanel != null) {
            cp.add(locationPanel, new GridBagConstraints(0, 1, 1, 1, 1., 0.,
                    GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(
                            0, 0, 0, 0), 0, 0));
        }
            
        JPanel buttonPanel = createButtonPanel();
        cp.add(buttonPanel, new GridBagConstraints(0, 2, 1, 1, 1., 0.,
                GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(
                        0, 0, 0, 0), 0, 0));
        
        // not displayed, only created;
        stTextArea = createStacktraceTextArea();
        stScroll = createStacktraceTextAreaScroll();
        setStackTraceText(excList.get(0));
        
        setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        pack();
        setLocationRelativeTo(null);
    }


    private static class TextAreaRenderer extends JTextArea implements ListCellRenderer
    {
        /**
         * 
         */
        private static final long serialVersionUID = -1151786934514170956L;

        public TextAreaRenderer()
        {	   
            setLineWrap(true);
	    setWrapStyleWord(true);
	    // setRows(10);
        }
        
        public Component getListCellRendererComponent(JList list, Object value,
            int index, boolean isSelected, boolean cellHasFocus)
        {                                     
            // if (index==0) setFont(getFont().deriveFont(Font.BOLD, 12)); else  
	    setFont(getFont().deriveFont(Font.PLAIN, 12)); 
            setText(value.toString());
            setBackground(isSelected ? list.getSelectionBackground() : null);
            setForeground(isSelected ? list.getSelectionForeground() : null);                                             
            return this;
        }
    }

//    // Test purposes:
//    public static void main(String[] args) {
//        RuntimeException ex = new RuntimeException("Runtime");
//        Error err = new Error("Some error");
//        Exception lex = new Exception("With a very, very, very, very, very, very, very, very, very, \n" +
//        		"very, very, very, very, very, very, very, very, very, very, very long message"); 
//        ParserException pex = new ParserException("With location", new Location("file", 22, 42));
//        List<Throwable> excs = Arrays.asList(ex, err, lex, pex);
//        
//        ExceptionDialog.showDialog((Frame)null, excs);
//        
//        ExceptionDialog.showDialog((Frame)null, new Exception("ABC"));
//        ExceptionDialog.showDialog((Frame)null, pex);
//    }
}
