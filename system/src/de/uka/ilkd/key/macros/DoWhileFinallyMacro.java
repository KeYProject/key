package de.uka.ilkd.key.macros;


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

/**
 * The abstract class DoWhileFinallyMacro can be used to create compound macros
 * which apply the macro given by {@link getProofMacro()} as long the given bound
 * of steps is not reached yet, the condition given by {@link getCondition()}
 * holds, and the macro is applicable. When this becomes false and the step bound
 * is not reached yet, the macro given by {@link getAltProofMacro()} is applied.
 *
 * @author Michael Kirsten
 */
public abstract class DoWhileFinallyMacro extends AbstractProofMacro {

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
	public boolean canApplyTo(KeYMediator mediator,
							  ImmutableList<Goal> goals,
							  PosInOccurrence posInOcc) {
        if (getCondition()) {
            return getProofMacro().canApplyTo(mediator, goals, posInOcc);
        } else {
            return getAltProofMacro().canApplyTo(mediator, goals, posInOcc);
        }
    }

    @Override
    public void applyTo(KeYMediator mediator,
                        ImmutableList<Goal> goals,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        int steps = getMaxSteps(mediator);
        while (steps > 0 && getCondition() && canApplyTo(mediator, goals, posInOcc)) {
            getProofMacro().applyTo(mediator, goals, posInOcc, listener);
            posInOcc = null;
            steps--;
        }
        if (steps > 0 && getAltProofMacro().canApplyTo(mediator, goals, posInOcc)) {
            getAltProofMacro().applyTo(mediator, goals, posInOcc, listener);
        }

    }

    /**
     * Gets the proof macro.
     *
     * @return the proofMacro.
     */
    abstract ProofMacro getProofMacro();

    /**
     * Gets the alternative proof macro for the else-branch.
     *
     * @return the proofMacro.
     */
    abstract ProofMacro getAltProofMacro();

    abstract boolean getCondition();

    /**
     * Returns the maximum number of rule applications allowed for
     * this macro. The default implementation is the maximum amount
     * of proof steps for automatic mode.
     * @return the maximum number of rule applications allowed for
     * this macro
     */
    static int getMaxSteps(KeYMediator mediator) {
		if (mediator.getSelectedProof() != null) {
			return mediator.getSelectedProof().getSettings().getStrategySettings().getMaxSteps();
		} else {
			return ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
		}
	}
}