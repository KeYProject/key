package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InfFlowPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;

public class FullInformationFlowAutoPilotMacro extends DoWhileFinallyMacro {

    /**
     * The number of proof steps that should be run by the {@link TryCloseMacro}
     * before retracting. This overrides the strategy setting if set to a value
     * greater or equal to 0.
     */
    private static final int NUMBER_OF_TRY_STEPS = -1;

    @Override
    public String getName() {
        return "Full Information Flow Auto Pilot";
    }

    @Override
    public String getDescription() {
        return "<html><ol><li>Search exhaustively for applicable position, then" +
                "<li>Start auxiliary computation" +
                "<li>Finish symbolic execution" +
                "<li>Try to close as many goals as possible" +
                "<li>Apply macro recursively" +
                "<li>Finish auxiliary computation" +
                "<li>Use information flow contracts" +
                "<li>Try to close as many goals as possible</ol>";
    }

    @Override
    ProofMacro getProofMacro() {
        final SequentialProofMacro stateExpansionAndCloseMacro =
                new SequentialProofMacro() {
                    @Override
                    protected ProofMacro[] createProofMacroArray() {
                        return new ProofMacro[] {
                                new StateExpansionAndInfFlowContractApplicationMacro(),
                                new TryCloseMacro(NUMBER_OF_TRY_STEPS) };
                    }
                    @Override
                    public String getName() { return ""; }
                    @Override
                    public String getDescription() { return "Anonymous Macro"; }
        };

        final SequentialProofMacro finishMainCompMacro =
                new SequentialOnLastGoalProofMacro() {
                    @Override
                    protected ProofMacro[] createProofMacroArray() {
                        return new ProofMacro[] { new FinishAuxiliaryComputationMacro(),
                                                  stateExpansionAndCloseMacro };
                    }
                    @Override
                    public String getName() { return ""; }
                    @Override
                    public String getDescription() { return "Anonymous Macro"; }
        };

        final AlternativeMacro alternativesMacro =
                new AlternativeMacro() {
                    @Override
                    public String getName() { return ""; }
                    @Override
                    public String getDescription() { return "Anonymous Macro"; }
                    @Override
                    protected ProofMacro[] createProofMacroArray() {
                        return new ProofMacro[] { new AuxiliaryComputationAutoPilotMacro(),
                                                  finishMainCompMacro };
                    }
        };

        return alternativesMacro;
    }

    @Override
    ProofMacro getAltProofMacro() {
        return new SkipMacro();
    }

    @Override
    boolean getCondition() {
        return true;
    }
    

    /**
     * {@inheritDoc}
     *
     * <p>
     * This compound macro is applicable if and only if the first macro is applicable.
     * If there is no first macro, this is not applicable.
     */
    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {

        final Proof proof = mediator.getSelectedProof();
        if (proof == null) {
            return false;
        }
        final Services services = proof.getServices();
        if (services == null) {
            return false;
        }
        final ProofOblInput poForProof =
                services.getSpecificationRepository().getProofOblInput(proof);
        return (poForProof instanceof InfFlowPO) && super.canApplyTo(mediator, goals, posInOcc);
    }
}