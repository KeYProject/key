package de.uka.ilkd.key.macros;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.settings.ProofSettings;

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
	public boolean canApplyTo(Proof proof,
	                          ImmutableList<Goal> goals,
	                          PosInOccurrence posInOcc) {
        if (getCondition()) {
            return getProofMacro().canApplyTo(proof, goals, posInOcc);
        } else {
            return getAltProofMacro().canApplyTo(proof, goals, posInOcc);
        }
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          Proof proof,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException, Exception {
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals);
        setMaxSteps(proof);
        int steps = getNumberSteps();
        final ProofMacro macro = getProofMacro();
        while (getNumberSteps() > 0 && getCondition() && macro.canApplyTo(proof, goals, posInOcc)) {
            final ProverTaskListener pml =
                    new ProofMacroListener(this, listener);
            pml.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, macro.getName(), 0));
            synchronized(macro) {
                // wait for macro to terminate
                info = macro.applyTo(uic, proof, goals, posInOcc, pml);
            }
            pml.taskFinished(info);
            steps -= info.getAppliedRules();
            setNumberSteps(steps);
            info = new ProofMacroFinishedInfo(this, info);
            goals = info.getGoals();
            proof = info.getProof();
            posInOcc = null;
        }
        final ProofMacro altMacro = getAltProofMacro();
        if (steps > 0 && altMacro.canApplyTo(proof, goals, posInOcc)) {
            final ProverTaskListener pml =
                    new ProofMacroListener(this, listener);
            pml.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, altMacro.getName(), 0));
            info = altMacro.applyTo(uic, proof, goals, posInOcc, pml);
            synchronized(altMacro) {
                // wait for macro to terminate
                info = new ProofMacroFinishedInfo(this, info);
            }
            pml.taskFinished(info);
        }
        return info;
    }

    /**
     * Gets the proof macro.
     *
     * @return the proofMacro.
     */
    protected abstract ProofMacro getProofMacro();

    /**
     * Gets the alternative proof macro for the else-branch.
     *
     * @return the proofMacro.
     */
    protected abstract ProofMacro getAltProofMacro();

    protected abstract boolean getCondition();

    /**
     * Sets the maximum number of rule applications allowed for
     * this macro. The default implementation is the maximum amount
     * of proof steps for automatic mode.
     * @return the maximum number of rule applications allowed for
     * this macro
     */
    protected void setMaxSteps(Proof proof) {
        final int steps;
        if (proof != null) {
            steps = proof.getSettings()
                         .getStrategySettings().getMaxSteps();
        } else {
            steps = ProofSettings.DEFAULT_SETTINGS
                    .getStrategySettings().getMaxSteps();
        }
        setNumberSteps(steps);
    }
}