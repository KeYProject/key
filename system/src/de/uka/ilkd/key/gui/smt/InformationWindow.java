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


import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.model.Model;


/**
 * The information window is used to present detailed information about the execution of a solver. 
 * In particular it presents information about:
 * - the concrete translation that was passed to the solver
 * - the translation of the taclets
 * - the messages that were sent between KeY and the external solvers.
 */
public class InformationWindow extends JDialog {

    private static final long serialVersionUID = 1L;
    
    private static String CE_HELP = "Bounded Counterexample Finder for KeY Proof Obligations"
    		+ "\n\n"
    		+ "- Shows a bounded model which satisfies the negation of the selected proof obligation"
    		+ "\n"
    		+ "- Only proof obligations without modalities are supported"
    		+ "\n"
    		+ "- The OneStepSimplifier neeeds to be activated, otherwise updates need to be handled manually beforehand"
    		+ "\n"
    		+ "- Double click ond location set, sequence and object nodes(inside a heap) to extend them"
    		+ "\n"
    		+ "- Choose bit sizes in Options -> SMT Solvers"
    		+ "\n"
    		+ "- We have indentified the following sources for spurious counterexample:"
    		+ "\n"
    		+ "   - Chosen bit sizes too small. Example: Bit size of Integer is 3 but literal 9 appears in proof obligation."
    		+ "\n"
    		+ "   - Finite type instances: Example: There is no maximum integer."
    		+ "\n"
    		+ "   - Removal of axioms. Example: There is a location set which contains location (o, f)";
    


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
	private Model model;
	public InformationWindow( SMTSolver solver, Collection<Information> information, String title){
		super();
		this.setTitle(title);
		initModel(solver);
		for(Information el : information){
	  getTabbedPane().addTab(el.title, newTab(el)); 
       }
       
       setSize(600, 500); 
       this.getContentPane().add(getTabbedPane());
       this.setModalExclusionType(ModalExclusionType.APPLICATION_EXCLUDE);
       this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
       this.setLocationByPlatform(true);
       
       
       this.setVisible(true);
   }
   
   private void initModel(SMTSolver solver){
	   if(solver.getType() != SolverType.Z3_CE_SOLVER){		   
		   return;
	   }
	   if(solver.getSocket().getQuery()==null){
		   return;
	   }
	   
	   Model m = solver.getSocket().getQuery().getModel();
	   this.model = m;
	   this.setTitle("Counterexample "+this.getTitle());
	   getTabbedPane().addTab("Counterexample", createModelTab());
	   createHelpTab();
   }
   
   private void createHelpTab(){
	   final JTextArea content = new JTextArea();
	   content.setEditable(false);
	   content.setText(CE_HELP);
	   JScrollPane pane = new JScrollPane();
	   pane.getViewport().add(content);
	   pane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
	   getTabbedPane().addTab("Help", pane);
   }
   
   private Component createModelTab(){

	   CETree tree = new CETree(model);
	   JScrollPane pane = new JScrollPane();
	   pane.getViewport().add(tree);
	   pane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
	   
	   return pane;

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
