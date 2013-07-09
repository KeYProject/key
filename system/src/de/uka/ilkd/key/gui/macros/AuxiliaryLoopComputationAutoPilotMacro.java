package de.uka.ilkd.key.gui.macros;

public class AuxiliaryLoopComputationAutoPilotMacro extends SequentialOnLastGoalProofMacro {

    /**
     * The number of proof steps that should be run by the {@link TryCloseMacro}
     * before retracting. This overrides the strategy setting.
     */
    private static final int NUMBER_OF_TRY_STEPS =
            Integer.getInteger("key.autopilot.closesteps", 1000);

    @Override
    public String getName() {
        return "Auxiliary Computation Auto Pilot";
    }

    @Override
    public String getDescription() {
        return "<html><ol><li>Start auxiliary computation" +
                "<li>Finish symbolic execution" +
                "<li>Try to close as many goals as possible</ol>";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        // The FinishSymbolicExecutionMacro and the TryCloseMacro shall be
        // started at the same node. Therefore they are encapsulated in an
        // own (anonymous) SequentialProofMacro.
        SequentialProofMacro finishSymbExecAndTryToClose =
                new SequentialProofMacro() {
            @Override
            protected ProofMacro[] createProofMacroArray() {
                return new ProofMacro[]{
                    new FinishSymbolicExecutionMacro(),
                    new TryCloseMacro(NUMBER_OF_TRY_STEPS)
                };
            }


            @Override
            public String getName() {
                return "Anonymous Macro";
            }


            @Override
            public String getDescription() {
                return "Anonymous Macro";
            }
        };
        return new ProofMacro[]{
            new StartAuxiliaryLoopComputationMacro(),
            finishSymbExecAndTryToClose,
        };
    }
}