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

import java.awt.event.ActionEvent;

import javax.swing.Icon;
import javax.swing.SwingWorker;

import de.uka.ilkd.key.core.AutoModeListener;
import de.uka.ilkd.key.core.InterruptListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.counterexample.AbstractCounterExampleGenerator;
import de.uka.ilkd.key.smt.counterexample.AbstractSideProofCounterExampleGenerator;

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
     * initialized with the KeYMediator.
     * <p>
     * <b>This class provides only the user interface and no counter example 
     * generation logic which is implemented by the 
     * {@link AbstractCounterExampleGenerator}</b>.
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

    @Override
    public void actionPerformed(ActionEvent e) {
       try {
          // Get required information
          Goal goal = getMediator().getSelectedGoal();
          Node node = goal.node();
          Proof oldProof = node.proof();
          Sequent oldSequent = node.sequent();
          // Start SwingWorker (CEWorker) in which counter example search is performed.
          getMediator().stopInterface(true);
          getMediator().setInteractive(false);
          CEWorker worker = new CEWorker(oldProof, oldSequent);
          getMediator().addInterruptedListener(worker);
          worker.execute();
       }
       catch (Exception exc) {
          ExceptionDialog.showDialog(mainWindow, exc);
       }
    }

    /**
     * Performs the {@link SemanticsBlastingMacro} in a side proof hidden to the 
     * user and shows the result with help of the {@link SolverListener}.
     */
    public static class NoMainWindowCounterExampleGenerator extends AbstractSideProofCounterExampleGenerator {
       /**
        * {@inheritDoc}
        */
       @Override
       protected SolverLauncherListener createSolverListener(SMTSettings settings, Proof proof) {
          return new SolverListener(settings, proof);
       }
    }
    
    /**
     * Performs the {@link SemanticsBlastingMacro} in a {@link Proof} registered
     * in the {@link MainWindow} and thus visible to the user. 
     * Results are shown with help of the {@link SolverListener}.
     * <p>
     * <b>This class provides only the user interface and no counter example 
     * generation logic which is implemented by the 
     * {@link AbstractCounterExampleGenerator}</b>.
     */
    public static class MainWindowCounterExampleGenerator extends AbstractCounterExampleGenerator {
       /**
        * {@inheritDoc}
        */
       @Override
       protected Proof createProof(KeYMediator mediator, Proof oldProof, Sequent oldSequent, String proofName) {
          Sequent newSequent = createNewSequent(oldSequent);
          InitConfig newInitConfig = oldProof.getInitConfig().deepCopy();
          Proof proof = new Proof(proofName,
                  newSequent, "",
                  newInitConfig.createTacletIndex(),
                  newInitConfig.createBuiltInRuleIndex(),
                  newInitConfig );

          proof.setEnv(oldProof.getEnv());
          proof.setNamespaces(oldProof.getNamespaces());

          ProofAggregate pa = new SingleProof(proof, "XXX");

          MainWindow mw = MainWindow.getInstance();
          mw.addProblem(pa);

          Services services = mw.getMediator().getServices();
          SpecificationRepository spec = services.getSpecificationRepository();
          spec.registerProof(spec.getProofOblInput(oldProof), proof);
          
          mediator.goalChosen(proof.getGoal(proof.root()));

          return proof;
       }

       /**
        * {@inheritDoc}
        */
       @Override
       protected void semanticsBlastingCompleted(KeYMediator mediator) {
          mediator.setInteractive(true);
          mediator.startInterface(true);
       }
       
       /**
        * {@inheritDoc}
        */
       @Override
       protected SolverLauncherListener createSolverListener(SMTSettings settings, Proof proof) {
          return new SolverListener(settings, proof);
       }
    }
    
    private class CEWorker extends SwingWorker<Void, Void> implements InterruptListener {
        private final Proof oldProof; 
        private final Sequent oldSequent;

        public CEWorker(Proof oldProof, Sequent oldSequent) {
           this.oldProof = oldProof;
           this.oldSequent = oldSequent;
        }

        @Override
        protected Void doInBackground() throws Exception {
//           new MainWindowCounterExampleGenerator().searchCounterExample(getMediator(), oldProof, oldSequent);
           new NoMainWindowCounterExampleGenerator().searchCounterExample(getMediator(), oldProof, oldSequent);
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
