/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen;

import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.core.InterruptListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.testgen.smt.testgen.AbstractTestGenerator;
import de.uka.ilkd.key.testgen.smt.testgen.StopRequest;

import org.key_project.prover.sequent.Sequent;

import org.jspecify.annotations.Nullable;

/**
 * <strong>The worker must be started using method {@link TGWorker#start()} and not
 * via the standard {@link #execute()}</strong>.
 */
public class TGWorker extends SwingWorker<Void, Void> implements InterruptListener, StopRequest {
    private final TGInfoDialog tgInfoDialog;
    private boolean stop;
    private final MainWindowTestGenerator testGenerator;
    private @Nullable Proof originalProof;

    /**
     * The getter calls below happen on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here, suppressed with a scoped key.
     * The selected proof is required: this worker is only started with a loaded proof (the
     * explicit NPE is crash-equivalent to the pre-existing latent NPE in the auto-mode calls).
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public TGWorker(TGInfoDialog tgInfoDialog) {
        this.tgInfoDialog = tgInfoDialog;
        Proof p = getMediator().getSelectedProof();
        if (p == null) {
            throw new NullPointerException("No proof selected for test generation.");
        }
        this.originalProof = p;
        this.testGenerator = new MainWindowTestGenerator(getMediator(), p, false);
    }

    public void start() {
        final KeYMediator mediator = getMediator();
        Proof p = originalProof;
        if (p == null) {
            throw new NullPointerException("No proof selected for test generation.");
        }
        mediator.initiateAutoMode(p, true, false);
        mediator.addInterruptedListener(this);
        execute();
    }

    @Override
    public Void doInBackground() throws InterruptedException {
        testGenerator.generateTestCases(this, tgInfoDialog.getLogger());
        return null;
    }

    /*
     * finalise the GUI stuff
     */
    @Override
    public void done() {
        Proof p = originalProof;
        if (p == null) {
            throw new NullPointerException("No proof selected for test generation.");
        }
        getMediator().finishAutoMode(p, true, true, null);
        getMediator().removeInterruptedListener(this);
        originalProof = null;
    }

    @Override
    public void interruptionPerformed() {
        cancel(true);
        tgInfoDialog.getLogger().writeln("\nStopping test case generation.");
        stop = true;
        testGenerator.stopSMTLauncher();
    }

    private KeYMediator getMediator() {
        return MainWindow.getInstance().getMediator();
    }

    public @Nullable Proof getOriginalProof() {
        return originalProof;
    }

    @Override
    public boolean shouldStop() {
        return stop;
    }

}


/**
 * Registers created {@link Proof}s in the {@link MainWindow} visible to the user.
 * <p>
 * <b>This class provides only the user interface and no test generation logic which is implemented
 * by the {@link AbstractTestGenerator}</b>.
 */
class MainWindowTestGenerator extends AbstractTestGenerator {
    /**
     * Defines if created {@link Proof}s are visible in the {@link MainWindow} or not.
     */
    private final boolean showInMainWindow;

    private final KeYMediator mediator;

    /**
     * Constructor.
     *
     * @param mediator The {@link KeYMediator} to use.
     * @param originalProof The {@link Proof} to generate test cases for.
     * @param showInMainWindow Defines if created {@link Proof}s are visible in the
     *        {@link MainWindow} or not.
     */
    public MainWindowTestGenerator(KeYMediator mediator, Proof originalProof,
            boolean showInMainWindow) {
        super(mediator.getUI(), originalProof);
        this.mediator = mediator;
        this.showInMainWindow = showInMainWindow;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void dispose() {
        if (showInMainWindow) {
            List<Proof> proofs = getProofs();
            for (final Proof p : proofs) {
                if (MainWindow.getInstance().getProofList().containsProof(p)) {
                    p.dispose();
                }
            }
            mediator.getSelectionModel().setSelectedProof(super.getOriginalProof());
        } else {
            super.dispose();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Proof createProof(UserInterfaceControl ui, Proof oldProof, String newName,
            Sequent newSequent) throws ProofInputException {
        if (showInMainWindow) {
            InitConfig initConfig = oldProof.getInitConfig();
            if (initConfig == null) {
                throw new NullPointerException("Proof has no initial configuration.");
            }
            final Proof proof = new Proof(newName, newSequent, null, initConfig.createTacletIndex(),
                initConfig.createBuiltInRuleIndex(), initConfig.deepCopy());
            ProofEnvironment env = oldProof.getEnv();
            if (env == null) {
                throw new NullPointerException("Proof has no proof environment.");
            }
            proof.setEnv(env);
            proof.setNamespaces(oldProof.getNamespaces());

            Services services = mediator.getServices();
            if (services == null) {
                throw new NullPointerException("Mediator has no services.");
            }
            SpecificationRepository spec = services.getSpecificationRepository();
            ProofOblInput po = spec.getProofOblInput(oldProof);
            if (po == null) {
                throw new NullPointerException("No proof obligation available for the proof.");
            }
            spec.registerProof(po, proof);
            final ProofAggregate pa = new SingleProof(proof, "XXX");
            ui.registerProofAggregate(pa);
            return proof;
        } else {
            return super.createProof(ui, oldProof, newName, newSequent);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void handleAllProofsPerformed(UserInterfaceControl ui) {
        mediator.setInteractive(true);
        mediator.startInterface(true);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void selectProof(UserInterfaceControl ui, Proof proof) {
        if (showInMainWindow) {
            mediator.getSelectionModel().setSelectedProof(proof);
        }
    }
}
