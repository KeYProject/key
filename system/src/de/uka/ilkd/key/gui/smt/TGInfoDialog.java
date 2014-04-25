package de.uka.ilkd.key.gui.smt;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.util.Collection;

import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.text.DefaultCaret;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.testgen.TestCaseGenerator;

@SuppressWarnings("serial")
public class TGInfoDialog extends JDialog implements SolverLauncherListener{
	
	private JTextArea textArea;
	
	private JButton stopButton;
	
	private JButton exitButton;
	
	private JButton startButton;
	
	
	
	
	
	

	@SuppressWarnings("serial")
	public TGInfoDialog() {
		super();
		
		 textArea = new JTextArea();
		 this.setLayout(new BorderLayout());
		 JScrollPane scrollpane = new JScrollPane(textArea);
		 scrollpane.setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		 scrollpane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
		 DefaultCaret caret = (DefaultCaret) textArea.getCaret();
         caret.setUpdatePolicy(DefaultCaret.ALWAYS_UPDATE);
         
         
         stopButton = new JButton(new AbstractAction("Stop") {			
			@Override
			public void actionPerformed(ActionEvent e) {
				MainWindow.getInstance().getMediator().stopAutoMode();	
				exitButton.setEnabled(true);
			}
		});
         
         exitButton = new JButton(new AbstractAction("Exit") {			
			@Override
			public void actionPerformed(ActionEvent e) {
				TGInfoDialog.this.dispose();				
			}
		});
         
         exitButton.setEnabled(false);
         
         JPanel flowPanel = new JPanel(new FlowLayout());
         flowPanel.add(stopButton);
         flowPanel.add(exitButton);
         
         
         
		 this.getContentPane().add(scrollpane, BorderLayout.CENTER);
		 this.getContentPane().add(flowPanel, BorderLayout.SOUTH);
		 this.setModal(false);
		 //this.pack();
		 this.setTitle("Test Suite Generation");
		 this.setSize(400, 200);		 
		 this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
		 this.setVisible(true);
		
	}
	
	public void write(String t){
		textArea.append(t);
	}

	public void writeln(String line){
		textArea.append(line+"\n");
	}

	@Override
	public void launcherStopped(SolverLauncher launcher,
			Collection<SMTSolver> problemSolvers) {
		
		writeln("Finished solving SMT problems: "+problemSolvers.size());
		TestCaseGenerator tg = new TestCaseGenerator();
		tg.setLogger(this);
		tg.setJUnit(TGOptionsDialog.isJunit());
		tg.generateJUnitTestSuite(problemSolvers);
		exitButton.setEnabled(true);
		
	}

	@Override
	public void launcherStarted(Collection<SMTProblem> problems,
			Collection<SolverType> solverTypes, SolverLauncher launcher) {
		writeln("Test data generation: solving SMT problems... \n please wait...");
		
		
	}
	
	
	
	

}
