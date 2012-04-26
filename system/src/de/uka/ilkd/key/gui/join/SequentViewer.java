package de.uka.ilkd.key.gui.join;


import javax.swing.JTextPane;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;


public class SequentViewer extends JTextPane{

        private static final long serialVersionUID = 1L;

          
        public SequentViewer(){
                setEditable(false);
                //this.add(new JScrollPane(getTextArea()));
                      
                
          
        }

        
        public void clear(){
                setText("");
        }
        
        public void setSequent(Sequent sequent, Services services){
                if(services != null){
                        LogicPrinter printer = new LogicPrinter(new ProgramPrinter(),
                                                              new NotationInfo(),
                                                              services);
                        printer.printSequent(sequent);
                        setText(printer.toString());
                }
        }
        
        
        
    

}