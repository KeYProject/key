package de.uka.ilkd.key.gui.testgen;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.util.Collection;
import java.util.Vector;

import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneConstants;
import javax.swing.WindowConstants;
import javax.swing.text.DefaultCaret;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.testgen.TestCaseGenerator;

@SuppressWarnings("serial")
public class TGInfoDialog extends JDialog implements SolverLauncherListener {
	private final JTextArea textArea;
	private final JButton stopButton;
	private final JButton exitButton;
	private final JButton startButton;
	
	private TGWorker worker;

	public TGInfoDialog() {
		super(MainWindow.getInstance());
		textArea = new JTextArea();
		setLayout(new BorderLayout());
		final JScrollPane scrollpane = new JScrollPane(textArea);
		scrollpane
		        .setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		scrollpane
		        .setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS);
		final DefaultCaret caret = (DefaultCaret) textArea.getCaret();
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
		startButton = new JButton(new AbstractAction("Start") {
			@Override
			public void actionPerformed(ActionEvent e) {
				KeYMediator mediator = MainWindow.getInstance().getMediator();
				mediator.stopInterface(true);
				mediator.setInteractive(false);				
				worker = new TGWorker(TGInfoDialog.this);
				mediator.addInterruptedListener(worker);
				worker.execute();
			}
		});
		exitButton.setEnabled(false);
		final JPanel flowPanel = new JPanel(new FlowLayout());
		flowPanel.add(startButton);
		flowPanel.add(stopButton);
		flowPanel.add(exitButton);
		getContentPane().add(scrollpane, BorderLayout.CENTER);
		getContentPane().add(flowPanel, BorderLayout.SOUTH);
		getContentPane().add(new TestGenOptionsPanel(), BorderLayout.EAST);
		setModal(false);
		// this.pack();
		setTitle("Test Suite Generation");
		this.setSize(700, 300);
		setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
		setLocationRelativeTo(MainWindow.getInstance());
		setVisible(true);
	}

	public Collection<SMTSolver> filterSolverResultsAndShowSolverStatistics(
	        Collection<SMTSolver> problemSolvers) {
		int unknown = 0;
		int infeasiblePaths = 0;
		int solvedPaths = 0;
		int problem = 0;
		final Vector<SMTSolver> output = new Vector<SMTSolver>();
		for (final SMTSolver solver : problemSolvers) {
			try {
				final SMTSolverResult.ThreeValuedTruth res = solver
				        .getFinalResult().isValid();
				if (res == SMTSolverResult.ThreeValuedTruth.UNKNOWN) {
					unknown++;
				} else if (res == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE) {
					solvedPaths++;
					if (solver.getSocket().getQuery() != null) {
						final Model m = solver.getSocket().getQuery()
						        .getModel();
						if (TestCaseGenerator.modelIsOK(m)) {
							output.add(solver);
						} else {
							problem++;
						}
					} else {
						problem++;
					}
				} else if (res == SMTSolverResult.ThreeValuedTruth.VALID) {
					infeasiblePaths++;
				}
			} catch (final Exception ex) {
				writeln(ex.getMessage());
			}
		}
		writeln("--- SMT Solver Results ---\n" + " solved pathconditions:"
		        + solvedPaths + "\n" + " invalid pre-/pathconditions:"
		        + infeasiblePaths + "\n" + " unknown:" + unknown);
		if (problem > 0) {
			writeln(" problems             :" + problem);
		}
		if (unknown > 0) {
			writeln(" Adjust the SMT solver settings (e.g. timeout) in Options->SMT Solvers and restart key.\n Make sure you use Z3 version 4.3.1.");
		}
		writeln("----------------------");
		return output;
	}

	@Override
	public void launcherStarted(Collection<SMTProblem> problems,
	        Collection<SolverType> solverTypes, SolverLauncher launcher) {
		writeln("Test data generation: solving SMT problems... \n please wait...");
	}

	@Override
	public void launcherStopped(SolverLauncher launcher,
	        Collection<SMTSolver> problemSolvers) {
		writeln("Finished solving SMT problems: " + problemSolvers.size());
		final TestCaseGenerator tg = new TestCaseGenerator(worker.getOriginalProof());
		tg.setLogger(this);
		problemSolvers = filterSolverResultsAndShowSolverStatistics(problemSolvers);
		if (problemSolvers.size() > 0) {
			tg.generateJUnitTestSuite(problemSolvers);
			if (tg.isJunit()) {
				writeln("Test oracle not yet implemented for JUnit.");
			} else {
				writeln("Compile and run the file with openjml!");
			}
		} else {
			writeln("No test data was generated.");
		}
		exitButton.setEnabled(true);
	}

	public void write(String t) {
		textArea.append(t);
	}

	public void writeln(String line) {
		textArea.append(line + "\n");
	}
}
