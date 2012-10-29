package de.uka.ilkd.key.gui.macros;

public class FullAutoPilotProofMacro extends SequentialProofMacro {

    @Override 
    public String getName() {
        return "Full Auto Pilot";
    }

    @Override 
    public String getDescription() {
        return "<html><ol><li>Finish symbolic execution" +
                "<li>Separate proof obligations" +
                "<li>Expand invariant definitions" +
                "<li>Try to close all proof obligations</ol>";
    }

    @Override 
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] {
                new AutoPilotPrepareProofMacro(),
                new TryCloseMacro()
        };
    }

}
