package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

import javax.swing.KeyStroke;

public class FullInformationFlowAutoPilotMacro extends AbstractProofMacro {

    /**
     * The number of proof steps that should be run by the {@link TryCloseMacro}
     * before retracting. This overrides the strategy setting if set to a value
     * greater or equal to 0.
     */
    private static final int NUMBER_OF_TRY_STEPS = -1;

    private final ProofMacro wrappedMacro;

    public FullInformationFlowAutoPilotMacro() {
        wrappedMacro = createProofMacro();
    }

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
    public boolean finishAfterMacro() {
        return true;
    }

    private ProofMacro createProofMacro() {
        final SequentialProofMacro stateExpansionAndCloseMacro =
                new SequentialProofMacro() {
            @Override
            public boolean finishAfterMacro() { return false; }
            @Override
            protected ProofMacro[] createProofMacroArray() {
                return new ProofMacro[] {
                        new StateExpansionAndInfFlowContractApplicationMacro() {
                            @Override
                            public boolean finishAfterMacro() { return false; }
                            },new TryCloseMacro(NUMBER_OF_TRY_STEPS) {
                                    @Override
                                    public boolean finishAfterMacro() { return false; }}};
            }
            @Override
            public String getName() { return "Anonymous Macro"; }
            @Override
            public String getDescription() { return "Anonymous Macro"; }
        };
        final SequentialProofMacro finishMainCompMacro =
                new SequentialOnLastGoalProofMacro() {
            @Override
            protected ProofMacro[] createProofMacroArray() {
                return new ProofMacro[] {
                        new FinishAuxiliaryComputationMacro() {
                            @Override
                            public boolean finishAfterMacro() { return false; }},
                            stateExpansionAndCloseMacro};}
            @Override
            public String getName() { return "Anonymous Macro"; }
            @Override
            public String getDescription() { return "Anonymous Macro"; }
            @Override
            public boolean finishAfterMacro() { return false; }
        };
        final AlternativeMacro alternativesMacro =
                new AlternativeMacro() {
                    @Override
                    public String getName() { return "Anonymous Macro"; }
                    @Override
                    public String getDescription() { return "Anonymous Macro"; }
                    @Override
                    public boolean finishAfterMacro() { return false; }
                    @Override
                    protected ProofMacro[] createProofMacroArray() {
                        return new ProofMacro[] {new AuxiliaryComputationAutoPilotMacro() {
                                                        @Override
                                                        public boolean finishAfterMacro() { return false; }},
                                                 finishMainCompMacro};}
        };
        return new DoWhileFinallyMacro() {
            @Override
            ProofMacro getProofMacro() { return alternativesMacro; }
            @Override
            ProofMacro getAltProofMacro() { return new SkipMacro(); }
            @Override
            boolean getCondition() { return true; }};
    }


    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        return wrappedMacro.canApplyTo(mediator, goals, posInOcc);
    }


    @Override
    public void applyTo(KeYMediator mediator,
                        ImmutableList<Goal> goals,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        wrappedMacro.applyTo(mediator, goals, posInOcc, listener);
    }


    @Override
    public KeyStroke getKeyStroke() {
        return null;  // default implementation
    }
}