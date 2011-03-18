package de.uka.ilkd.key.gui.smt;

import java.awt.Component;
import java.awt.ScrollPane;
import java.util.Collection;

import javax.swing.JDialog;
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
       this.setTitle(title);
       this.setVisible(true);
   }
   
   private Component newTab(Information information){
       ScrollPane pane = new ScrollPane();
       pane.add(new JTextArea(information.content));
       return pane;
   }
   
   
   private JTabbedPane getTabbedPane(){
       if(tabbedPane == null){
	   tabbedPane = new JTabbedPane();
       }
       return tabbedPane;
   }
   
   
}
