package de.uka.ilkd.key.macros;

public class StartAuxiliaryComputationMacro extends AlternativeMacro {

    @Override
    public String getName() {
        return "Start auxiliary computation for self-composition proofs";
    }

    @Override
    public String getDescription() {
        return "In order to increase the efficiency of self-composition " +
                "proofs, this macro starts a side calculation which does " +
                "the symbolic execution only once. The result is " +
                "instantiated twice with the variable to be used in the " +
                "two executions of the self-composition.";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] {new StartAuxiliaryMethodComputationMacro(),
                                 new StartAuxiliaryLoopComputationMacro(),
                                 new StartAuxiliaryBlockComputationMacro()};
    }

}