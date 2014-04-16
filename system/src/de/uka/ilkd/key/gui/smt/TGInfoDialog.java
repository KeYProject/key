package de.uka.ilkd.key.gui.smt;

import java.awt.BorderLayout;
import java.util.Collection;

import javax.swing.JDialog;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.text.DefaultCaret;

import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.testgen.TestCaseGenerator;

public class TGInfoDialog extends JDialog implements SolverLauncherListener{
	
	private JTextArea text;
	
	
	
	

	public TGInfoDialog() {
		super();
		
		 text = new JTextArea();
		 this.setLayout(new BorderLayout());
		 JScrollPane scrollpane = new JScrollPane(text);
		 scrollpane.setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		 scrollpane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
		 DefaultCaret caret = (DefaultCaret) text.getCaret();
         caret.setUpdatePolicy(DefaultCaret.ALWAYS_UPDATE);
		 this.getContentPane().add(scrollpane);
		 this.setModal(false);
		 //this.pack();
		 this.setTitle("Generate Counterexamples");
		 this.setSize(400, 200);		 
		 this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
		 this.setVisible(true);
		
	}
	
	public void write(String t){
		text.append(t);
	}

	public void writeln(String line){
		text.append(line+"\n");
	}

	@Override
	public void launcherStopped(SolverLauncher launcher,
			Collection<SMTSolver> problemSolvers) {
		
		writeln("Stoped solving SMT problems: "+problemSolvers.size());
		TestCaseGenerator tg = new TestCaseGenerator();
		tg.setLogger(this);
		tg.generateJUnitTestSuite(problemSolvers);
		
	}

	@Override
	public void launcherStarted(Collection<SMTProblem> problems,
			Collection<SolverType> solverTypes, SolverLauncher launcher) {
		writeln("Test data generation: Start solving SMT problems (Z3 version 4.3.1 is required)... \n please wait...");
		
		
	}
	
	
	
	

}
