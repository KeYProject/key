package de.uka.ilkd.key.macros;

public class FinishAuxiliaryComputationMacro extends AlternativeMacro {

    @Override
    public String getName() {
        return "Finish auxiliary computation";
    }

    @Override
    public String getDescription() {
        return "Finish auxiliary computation";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] { new FinishAuxiliaryMethodComputationMacro(),
                                  new FinishAuxiliaryLoopComputationMacro(),
                                  new FinishAuxiliaryBlockComputationMacro()};
    }
}