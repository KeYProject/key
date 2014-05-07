package de.uka.ilkd.key.gui.macros;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.logic.PosInOccurrence;

public class DoWhileElseMacro implements ProofMacro {

    ProofMacro macro;
    ProofMacro elseMacro;
    boolean condition;
    int steps;

    public DoWhileElseMacro(ProofMacro macro, ProofMacro elseMacro,
                            int steps, boolean condition) {
        this.macro = macro;
        this.elseMacro = elseMacro;
        this.condition = condition;
        this.steps = steps;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#getName()
     */
    @Override
    public String getName() {
        return "Apply macro as long as condition is met, then apply other macro";
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#getDescription()
     */
    @Override
    public String getDescription() {
        return "Applies specificed macro as long as specified condition is met" +
                "with no more rule applications than specified. If the" +
                "macro is not applicable anymore and the maximum steps" +
                "are not reached yet, then apply other macro once.";
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        if (getCondition()) {
            return getProofMacro().canApplyTo(mediator, posInOcc);
        } else {
            return getAltProofMacro().canApplyTo(mediator, posInOcc);
        }
    }

    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        int steps = getMaxSteps(mediator);
        while (steps > 0 && getCondition()) {
            getProofMacro().applyTo(mediator, posInOcc, listener);
        }
        if (steps > 0) {
            getAltProofMacro().applyTo(mediator, posInOcc, listener);
        }

    }

    /**
     * Gets the proof macro.
     *
     * @return the proofMacro.
     */
    ProofMacro getProofMacro() {
        return this.macro;
    }

    /**
     * Gets the alternative proof macro for the else-branch.
     *
     * @return the proofMacro.
     */
    ProofMacro getAltProofMacro() {
        return this.elseMacro;
    }

    boolean getCondition() {
        return this.condition;
    }

    /** returns the maximum number of rule applications allowed for
     * this macro. The default implementation is the maximum amount
     * of proof steps for automatic mode.
     * @return the maximum number of rule applications allowed for
     * this macro
     */
    int getMaxSteps(KeYMediator mediator) {
        if (this.steps <= 0) {
            if (mediator.getSelectedProof() != null) {
                return mediator.getSelectedProof().getSettings().getStrategySettings().getMaxSteps();
            } else {
                return ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
            }
        } else {
            return steps;
        }
    }

    @Override
    public KeyStroke getKeyStroke() {
        return null; // default implementation
    }
}