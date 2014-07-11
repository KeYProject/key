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

    private ProofMacro createProofMacro() {
        final SequentialProofMacro stateExpansionAndCloseMacro =
                new SequentialProofMacro() {
            @Override
            protected ProofMacro[] createProofMacroArray() {
                return new ProofMacro[] {
                        new StateExpansionAndInfFlowContractApplicationMacro(),
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
                return new ProofMacro[] {
                        new FinishAuxiliaryComputationMacro(),
                            stateExpansionAndCloseMacro};}
            @Override
            public String getName() { return "Anonymous Macro"; }
            @Override
            public String getDescription() { return "Anonymous Macro"; }
        };
        final AlternativeMacro alternativesMacro =
                new AlternativeMacro() {
                    @Override
                    public String getName() { return "Anonymous Macro"; }
                    @Override
                    public String getDescription() { return "Anonymous Macro"; }
                    @Override
                    protected ProofMacro[] createProofMacroArray() {
                        return new ProofMacro[] {new AuxiliaryComputationAutoPilotMacro(),
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
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException {
        final ProverTaskListener cptl =
                new ProofMacroListener(wrappedMacro, listener);
        cptl.taskStarted(wrappedMacro.getName(), 0);
        ProofMacroFinishedInfo info = wrappedMacro.applyTo(mediator, goals,
                                                           posInOcc, cptl);
        cptl.taskFinished(info);
        info = new ProofMacroFinishedInfo(this, info);
        return info;
    }


    @Override
    public KeyStroke getKeyStroke() {
        return null;  // default implementation
    }
}