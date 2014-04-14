package de.uka.ilkd.key.gui.smt;

import java.awt.BorderLayout;
import java.util.Collection;

import javax.swing.JDialog;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

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
		 this.getContentPane().add(scrollpane);
		 this.setModal(false);
		 //this.pack();
		 this.setTitle("Generate Counterexamples");
		 this.setSize(300, 200);
		 this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
		 this.setVisible(true);
		
	}
	
	public void write(String line){
		text.setText(text.getText()+"\n"+line);
		text.setCaretPosition(text.getText().length()-1);
	}

	@Override
	public void launcherStopped(SolverLauncher launcher,
			Collection<SMTSolver> problemSolvers) {
		
		write("Stoped solving smt problems: "+problemSolvers.size());
		TestCaseGenerator tg = new TestCaseGenerator();
		tg.setLogger(this);
		tg.generateJUnitTestSuite(problemSolvers);
		
	}

	@Override
	public void launcherStarted(Collection<SMTProblem> problems,
			Collection<SolverType> solverTypes, SolverLauncher launcher) {
		write("Start solving smt problems");
		
		
	}
	
	
	
	

}
