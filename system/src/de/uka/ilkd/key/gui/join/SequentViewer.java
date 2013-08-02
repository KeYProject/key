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