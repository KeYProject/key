package de.uka.ilkd.key.gui.macros;

public class FinishAuxiliaryComputationMacro extends AlternativeProofMacro {

    @Override
    public String getName() {
        return "Finish auxiliary computation";
    }

    @Override
    public String getDescription() {
        return "Finish auxiliary computation";
    }

    @Override
    protected ExtendedProofMacro[] createProofMacroArray() {
        return new ExtendedProofMacro[] { new ProofMacroWrapper(
                                              new FinishAuxiliaryMethodComputationMacro()),
                                          new ProofMacroWrapper(
                                              new FinishAuxiliaryLoopComputationMacro()),
                                          new ProofMacroWrapper(
                                              new FinishAuxiliaryBlockComputationMacro())};
    }

}