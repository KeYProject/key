package de.uka.ilkd.key.gui.testgen;

import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import javax.swing.SwingWorker;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.InterruptListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.gui.smt.ProofIndependentSMTSettings;
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.util.Debug;

public class TGWorker extends SwingWorker<Void, Void> implements InterruptListener {
	private TGInfoDialog tgInfoDialog;
	private boolean stop;
	private SolverLauncher launcher;
	private Vector<Proof> proofs;
	private Proof originalProof;
	
	public TGWorker(TGInfoDialog tgInfoDialog){
		this.tgInfoDialog = tgInfoDialog;
	}

	@Override
	public Void doInBackground() {

		TestGenerationSettings settings = ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings();


		if (!SolverType.Z3_CE_SOLVER.isInstalled(true)) {
			tgInfoDialog
			.writeln("Could not find the z3 SMT solver. Aborting.");
			return null;
		}
		if (!SolverType.Z3_CE_SOLVER.isSupportedVersion()) {
			tgInfoDialog.writeln("Warning: z3 supported versions are: "
					+ Arrays.toString(SolverType.Z3_CE_SOLVER
							.getSupportedVersions()));
		}
		tgInfoDialog
		.writeln("Extracting test data constraints (path conditions).");
		proofs = createProofsForTesting(getMediator(),
				settings.removeDuplicates());
		if (stop) {
			return null;
		}
		if (proofs.size() > 0) {
			tgInfoDialog.writeln("Extracted " + proofs.size()
					+ " test data constraints.");
		} else {
			tgInfoDialog
			.writeln("No test data constraints were extracted.");
		}
		final KeYMediator mediator = getMediator();
		originalProof = mediator.getSelectedProof();
		final Collection<SMTProblem> problems = new LinkedList<SMTProblem>();
		tgInfoDialog
		.writeln("Test data generation: appling semantic blasting macro on proofs");
		for (final Proof proof : proofs) {
			if (stop) {
				return null;
			}
			tgInfoDialog.write(".");
			final ProofAggregate pa = new SingleProof(proof, "XXX");
			final MainWindow mw = MainWindow.getInstance();
			mw.addProblem(pa);
			final SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
			try {
				if (stop) {
					return null;
				}
				mediator.setProof(proof);
				macro.applyTo(mediator, null, null);
				problems.addAll(SMTProblem.createSMTProblems(mediator
						.getSelectedProof()));
				// mediator.getUI().removeProof(mediator.getSelectedProof());
			} catch (final InterruptedException e) {
				Debug.out("Semantics blasting interrupted");
				tgInfoDialog
				.writeln("\n Warning: semantics blasting was interrupted. A test case will not be generated.");
			} catch (final Exception e) {
				tgInfoDialog.writeln(e.getLocalizedMessage());
				System.err.println(e);
			}
		}
		tgInfoDialog.writeln("\nDone applying semantic blasting.");
		mediator.setProof(originalProof);
		// getMediator().setInteractive(true);
		// getMediator().startInterface(true);
		final Proof proof = mediator.getSelectedProof();

		//create special smt settings for test case generation
		final ProofIndependentSMTSettings piSettings = ProofIndependentSettings.DEFAULT_INSTANCE
				.getSMTSettings().clone();
		piSettings.setMaxConcurrentProcesses(settings.getNumberOfProcesses());
		final ProofDependentSMTSettings pdSettings = proof.getSettings()
				.getSMTSettings().clone();
		pdSettings.invariantForall = settings.invaraiantForAll();
		// invoke z3 for counterexamples
		final SMTSettings smtsettings = new SMTSettings(pdSettings,
				piSettings, proof);
		launcher = new SolverLauncher(smtsettings);
		launcher.addListener(tgInfoDialog);
		// launcher.addListener(new SolverListener(settings));
		final List<SolverType> solvers = new LinkedList<SolverType>();
		solvers.add(SolverType.Z3_CE_SOLVER);
		SolverType.Z3_CE_SOLVER.checkForSupport();
		if (stop) {
			return null;
		}
		if (Thread.interrupted()) {
			return null;
		}
		launcher.launch(solvers, problems, proof.getServices());
		return null;
	}

	/*
	 * finalise the GUI stuff
	 */
	@Override
	public void done() {
		removeGeneratedProofs();
		getMediator().setInteractive(true);
		getMediator().startInterface(true);
		getMediator().removeInterruptedListener(this);
		originalProof = null;
	}

	@Override
	public void interruptionPerformed() {
		cancel(true);
		tgInfoDialog.writeln("\nStopping test case generation.");
		stop = true;
		if (launcher != null) {
			launcher.stop();
		}
	}

	/**
	 * Removes all generated proofs.
	 */
	private void removeGeneratedProofs() {
		if (proofs == null) {
			return;
		}
		for (final Proof p : proofs) {
			if (MainWindow.getInstance().getProofList().containsProof(p)) {
				getMediator().getUI().removeProof(p);
				p.dispose();
			}
		}
		getMediator().setProof(originalProof);
	}

	

	private KeYMediator getMediator(){
		return MainWindow.getInstance().getMediator();
	}

	/**
	 * Creates a proof with the specified node as its root. If an identical
	 * proof is found in otherProofs than null will be returned instead.
	 * 
	 * @param node
	 * @param otherProofs
	 * @return
	 */
	private Proof createProofForTesting_noDuplicate(Node node,
			Vector<Proof> otherProofs) {
		// System.out.println("Create proof for test case from Node:"+node.serialNr());
		final Proof oldProof = node.proof();
		final Sequent oldSequent = node.sequent();
		Sequent newSequent = Sequent.createSequent(
				Semisequent.EMPTY_SEMISEQUENT, Semisequent.EMPTY_SEMISEQUENT);
		Iterator<SequentFormula> it = oldSequent.antecedent().iterator();
		while (it.hasNext()) {
			final SequentFormula sf = it.next();
			// Allow modailities in the antecedent
			if (hasModalities(sf.formula(), false)) {
				continue;
			}
			newSequent = newSequent.addFormula(sf, true, false).sequent();
		}
		it = oldSequent.succedent().iterator();
		while (it.hasNext()) {
			final SequentFormula sf = it.next();
			if (hasModalities(sf.formula(), true)) {
				continue;
			}
			newSequent = newSequent.addFormula(sf, false, false).sequent();
		}
		// Check if a proof with the same sequent already exists.
		if (otherProofs != null) {
			for (final Proof otherProof : otherProofs) {
				if (otherProof.root().sequent().equals(newSequent)) {
					// System.out.println("Found and skip duplicate proof for node:"+node.serialNr());
					return null;
				}
			}
		}
		final Proof proof = new Proof("Test Case for NodeNr: "
				+ node.serialNr(), newSequent, "", oldProof.env()
				.getInitConfig().createTacletIndex(), oldProof.env()
				.getInitConfig().createBuiltInRuleIndex(),
				oldProof.getServices(), oldProof.getSettings());
		proof.setProofEnv(oldProof.env());
		proof.setNamespaces(oldProof.getNamespaces());
		return proof;
	}

	/**
	 * Creates a proof for each open node if the selected proof is open and a
	 * proof for each node on which the emptyModality rules was applied if the
	 * selected proof is closed.
	 * 
	 * @param mediator
	 * @param removeDuplicatePathConditions
	 *            - if true no identical proofs will be created
	 * @return
	 */
	private Vector<Proof> createProofsForTesting(KeYMediator mediator,
			boolean removeDuplicatePathConditions) {
		final Vector<Proof> res = new Vector<Proof>();
		final Proof oldProof = mediator.getSelectedProof();
		originalProof = oldProof;
		final List<Node> nodes = new LinkedList<Node>();
		final ImmutableList<Goal> oldGoals = oldProof.openGoals();
		if (originalProof.closed()) {
			getNodesWithEmptyModalities(
					originalProof.root(), nodes);
		} else {
			for (final Goal goal : oldGoals) {
				nodes.add(goal.node());
			}
		}
		final Iterator<Node> oldGoalIter = nodes.iterator();
		while (oldGoalIter.hasNext()) {
			try {
				Proof p = null;
				if (removeDuplicatePathConditions) {
					p = createProofForTesting_noDuplicate(oldGoalIter.next(),
							res);
				} else {
					p = createProofForTesting_noDuplicate(oldGoalIter.next(),
							null);
				}
				if (p != null) {
					res.add(p);
				}
			} catch (final Exception e) {
				System.err.println(e.getMessage());
			}
		}
		return res;
	}

	/**
	 * Adds all nodes on which the emptyModality rule was applied to the list.
	 * 
	 * @param root
	 * @param nodes
	 */
	private void getNodesWithEmptyModalities(Node root, List<Node> nodes) {
		if (root.getAppliedRuleApp() != null) {
			final RuleApp app = root.getAppliedRuleApp();
			if (app.rule().name().toString().equals("emptyModality")) {
				nodes.add(root);
			}
		}
		for (int i = 0; i < root.childrenCount(); ++i) {
			getNodesWithEmptyModalities(root.child(i), nodes);
		}
	}

	private boolean hasModalities(Term t, boolean checkUpdates) {
		final JavaBlock jb = t.javaBlock();
		if (jb != null && !jb.isEmpty()) {
			// System.out.println("Excluded javablock");
			return true;
		}
		if (t.op() == UpdateApplication.UPDATE_APPLICATION && checkUpdates) {
			// System.out.println("Exclude update application.");
			return true;
		}
		boolean res = false;
		for (int i = 0; i < t.arity() && !res; i++) {
			res |= hasModalities(t.sub(i), checkUpdates);
		}
		return res;
	}
	
	public Proof getOriginalProof(){
		return originalProof;
	}
}
