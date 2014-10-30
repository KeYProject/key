package de.uka.ilkd.key.macros;

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
}