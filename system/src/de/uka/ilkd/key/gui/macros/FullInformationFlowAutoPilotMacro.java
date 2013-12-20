package de.uka.ilkd.key.gui.macros;

public class FullInformationFlowAutoPilotMacro extends
        ExhaustiveProofMacro {

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
        final ExhaustiveProofMacro exhaustiveAutoPilotMacro =
                new ExhaustiveProofMacro() {
                    @Override
                    public String getName() { return "Anonymous Macro"; }
                    @Override
                    public String getDescription() { return "Anonymous Macro"; }
                    @Override
                    ProofMacro getProofMacro() { return new AuxiliaryComputationAutoPilotMacro(); }
        };
        final SequentialProofMacro stateExpansionAndCloseMacro = new SequentialProofMacro() {
            @Override
            protected ProofMacro[] createProofMacroArray() {
                return new ProofMacro[] {new StateExpansionAndInfFlowContractApplicationMacro(),
                                         new TryCloseMacro(NUMBER_OF_TRY_STEPS)};
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
                return new ProofMacro[] {new FinishAuxiliaryComputationMacro(),
                                         stateExpansionAndCloseMacro};}
            @Override
            public String getName() { return "Anonymous Macro"; }
            @Override
            public String getDescription() { return "Anonymous Macro"; }
        };
        AlternativeProofMacro alternativesMacro =
                new AlternativeProofMacro() {
                    @Override
                    public String getName() { return "Anonymous Macro"; }
                    @Override
                    public String getDescription() { return "Anonymous Macro"; }
                    @Override
                    protected ProofMacro[] createProofMacroArray() {
                        return new ProofMacro[] {exhaustiveAutoPilotMacro,
                                                 finishMainCompMacro};}
        };
        return new DoWhileElseMacro(alternativesMacro, NUMBER_OF_TRY_STEPS);
    }
}