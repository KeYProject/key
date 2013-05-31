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


package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.Component;
import java.util.Collection;

import javax.swing.JDialog;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.Element;


/**
 * The information window is used to present detailed information about the execution of a solver. 
 * In particular it presents information about:
 * - the concrete translation that was passed to the solver
 * - the translation of the taclets
 * - the messages that were sent between KeY and the external solvers.
 */
public class InformationWindow extends JDialog {

    private static final long serialVersionUID = 1L;


    static class Information{
	final String content;
	final String title;
	final String solver;
	public Information(String title,String content,String solver) {
	    super();
	    this.content = content;
	    this.title = title;
	    this.solver = solver;
        }
	
    }
    
    private JTabbedPane tabbedPane;
   
   
   
   public InformationWindow(Collection<Information> information, String title){
       for(Information el : information){
	  getTabbedPane().addTab(el.title, newTab(el)); 
       }
       setSize(600, 500);
       this.getContentPane().add(getTabbedPane());
       this.setModalExclusionType(ModalExclusionType.APPLICATION_EXCLUDE);
       this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
       this.setLocationByPlatform(true);
       this.setTitle(title);
       this.setVisible(true);
   }
   
   private Component newTab(Information information){
	    final JTextArea lines = new JTextArea("1");
	    final JTextArea content = new JTextArea();
		 
		lines.setBackground(Color.LIGHT_GRAY);
		lines.setEditable(false);

		content.getDocument().addDocumentListener(new DocumentListener(){
			public String getText(){
				int caretPosition = content.getDocument().getLength();
				Element root = content.getDocument().getDefaultRootElement();
				String text = "1" + System.getProperty("line.separator");
				for(int i = 2; i < root.getElementIndex( caretPosition ) + 2; i++){
					text += i + System.getProperty("line.separator");
				}
				return text;
			}
			@Override
			public void changedUpdate(DocumentEvent de) {
				lines.setText(getText());
			}

			@Override
			public void insertUpdate(DocumentEvent de) {
				lines.setText(getText());
			}

			@Override
			public void removeUpdate(DocumentEvent de) {
				lines.setText(getText());
			}

		});
		content.setText(information.content);
		JScrollPane pane = new JScrollPane();
		pane.getViewport().add(content);
		pane.setRowHeaderView(lines);
		pane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
	   
     
        return pane;
   }
   
   
   private JTabbedPane getTabbedPane(){
       if(tabbedPane == null){
	   tabbedPane = new JTabbedPane();
       }
       return tabbedPane;
   }
   
   
}
