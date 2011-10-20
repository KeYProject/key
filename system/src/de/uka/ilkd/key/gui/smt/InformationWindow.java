// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.smt;

import java.awt.Component;
import java.util.Collection;

import javax.swing.JDialog;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;



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
       setSize(400, 300);
       this.getContentPane().add(getTabbedPane());
       this.setModalExclusionType(ModalExclusionType.APPLICATION_EXCLUDE);
       this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
       this.setLocationByPlatform(true);
       this.setTitle(title);
       this.setVisible(true);
   }
   
   private Component newTab(Information information){
       JScrollPane pane = new JScrollPane(new JTextArea(information.content));
        return pane;
   }
   
   
   private JTabbedPane getTabbedPane(){
       if(tabbedPane == null){
	   tabbedPane = new JTabbedPane();
       }
       return tabbedPane;
   }
   
   
}
