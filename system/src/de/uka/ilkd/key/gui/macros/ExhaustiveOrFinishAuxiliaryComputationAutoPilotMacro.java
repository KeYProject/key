package de.uka.ilkd.key.gui.macros;

public class ExhaustiveOrFinishAuxiliaryComputationAutoPilotMacro extends
        ExhaustiveProofMacro {

    /**
     * The number of proof steps that should be run by the {@link TryCloseMacro}
     * before retracting. This overrides the strategy setting if set to a value
     * greater or equal to 0.
     */
    private static final int NUMBER_OF_TRY_STEPS = -1;
//            Integer.getInteger("key.autopilot.closesteps", 1000);

    @Override
    public String getName() {
        return "Exhaustive Auxiliary Computation Auto Pilot";
    }

    @Override
    public String getDescription() {
        return "<html><ol><li>Search exhaustively for applicable position, then" +
        	"<li>Start auxiliary computation" +
                "<li>Finish symbolic execution" +
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
        final SequentialProofMacro m1 = new SequentialProofMacro() {
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
        final SequentialProofMacro fullmainCompMacro =
                new SequentialOnLastGoalProofMacro() {
            @Override
            protected ProofMacro[] createProofMacroArray() {
                return new ProofMacro[] {new FinishAuxiliaryComputationMacro(),
                                         m1};}
            @Override
            public String getName() { return "Anonymous Macro"; }
            @Override
            public String getDescription() { return "Anonymous Macro"; }
        };
        AlternativeProofMacro exhaustiveCompMacro =
                new AlternativeProofMacro() {
                    @Override
                    public String getName() { return "Anonymous Macro"; }
                    @Override
                    public String getDescription() { return "Anonymous Macro"; }
                    @Override
                    protected ProofMacro[] createProofMacroArray() {
                        return new ProofMacro[] {exhaustiveAutoPilotMacro,
                                                 fullmainCompMacro};}
        };
        return new DoWhileElseMacro(exhaustiveCompMacro, NUMBER_OF_TRY_STEPS);
    }
}