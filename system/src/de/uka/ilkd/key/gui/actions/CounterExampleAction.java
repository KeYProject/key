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
package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.util.Debug;
import java.awt.event.ActionEvent;
import java.util.*;
import javax.swing.*;

@SuppressWarnings("serial")
public class CounterExampleAction extends MainWindowAction {

    private static final String NAME = "Generate Counterexample";
    private static final String TOOLTIP = "Search for a counterexample for the selected goal";

    public CounterExampleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName(NAME);
        setTooltip(TOOLTIP);
        Icon icon = IconFactory.counterExample(MainWindow.TOOLBAR_ICON_SIZE);
        putValue(SMALL_ICON, icon);
        init();
    }

    /**
     * Registers the action at some listeners to update its status in a correct
     * fashion. This method has to be invoked after the Main class has been
     * initialised with the KeYMediator.
     */
    public void init() {
        final KeYSelectionListener selListener = new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                final Proof proof = getMediator().getSelectedProof();

                if (proof == null) {
                    // no proof loaded
                    setEnabled(false);
                } else {
                    final Node selNode = getMediator().getSelectedNode();
                    //Can be applied only to root nodes
                    
                    
                    
                    setEnabled(selNode.childrenCount() == 0 && !selNode.isClosed());
                }
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                selectedNodeChanged(e);
            }
        };
        getMediator().addKeYSelectionListener(selListener);
        getMediator().addAutoModeListener(new AutoModeListener() {
            @Override
            public void autoModeStarted(ProofEvent e) {
                getMediator().removeKeYSelectionListener(selListener);
                setEnabled(false);
            }

            @Override
            public void autoModeStopped(ProofEvent e) {
                getMediator().addKeYSelectionListener(selListener);
                selListener.selectedNodeChanged(null);
            }
        });
        selListener.selectedNodeChanged(new KeYSelectionEvent(getMediator().getSelectionModel()));
    }

    private Proof createProof(KeYMediator mediator) {
        Goal goal = mediator.getSelectedGoal();
        Node node = goal.node();
        Proof oldProof = node.proof();
        Sequent oldSequent = node.sequent();
        Sequent newSequent = Sequent.createSequent(oldSequent.antecedent(), oldSequent.succedent());
        InitConfig newInitConfig = oldProof.getInitConfig().deepCopy();
        Proof proof = new Proof("Semantics Blasting: " + oldProof.name(),
                newSequent, "",
                newInitConfig.createTacletIndex(),
                newInitConfig.createBuiltInRuleIndex(),
                newInitConfig );

        proof.setEnv(oldProof.getEnv());
        proof.setNamespaces(oldProof.getNamespaces());

        ProofAggregate pa = new SingleProof(proof, "XXX");

        MainWindow mw = MainWindow.getInstance();
        mw.addProblem(pa);

        mediator.goalChosen(proof.getGoal(proof.root()));

        return proof;

    }

    @Override
    public void actionPerformed(ActionEvent e) {
        createProof(getMediator());
        getMediator().stopInterface(true);
        getMediator().setInteractive(false);
        CEWorker worker = new CEWorker();
        getMediator().addInterruptedListener(worker);
        worker.execute();
    }

    private class CEWorker extends SwingWorker<Void, Void> implements InterruptListener {

        @Override
        protected Void doInBackground() throws Exception {
            final KeYMediator mediator = getMediator();
            final Proof proof = mediator.getSelectedProof();
            final SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
            TaskFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
            final ProverTaskListener ptl = mediator.getUI().getListener();
            ptl.taskStarted(macro.getName(), 0);

            try {
                synchronized(macro) {
                    // wait for macro to terminate
                    info = macro.applyTo(mediator, null, ptl);
                }
            } catch (InterruptedException e) {
                Debug.out("Semantics blasting interrupted");
            } finally {
                ptl.taskFinished(info);
                getMediator().setInteractive(true);
                getMediator().startInterface(true);
            }

            //invoke z3 for counterexamples
            SMTSettings settings = new SMTSettings(proof.getSettings().getSMTSettings(),
                    ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(), proof);
            SolverLauncher launcher = new SolverLauncher(settings);
            launcher.addListener(new SolverListener(settings));

            List<SolverType> solvers = new LinkedList<SolverType>();
            solvers.add(SolverType.Z3_CE_SOLVER);

            launcher.launch(solvers,
                    SMTProblem.createSMTProblems(proof),
                    proof.getServices());

            return null;
        }

        @Override
        public void interruptionPerformed() {
            cancel(true);
        }

        @Override
        protected void done() {
            getMediator().setInteractive(true);
            getMediator().startInterface(true);
            getMediator().removeInterruptedListener(this);
        }
    }
}
