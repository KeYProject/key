package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.macros.AlternativeMacro;
import de.uka.ilkd.key.macros.ProofMacro;

public class FinishAuxiliaryComputationMacro extends AlternativeMacro {

    @Override
    public String getName() {
        return "Finish auxiliary computation";
    }

    @Override
    public String getCategory() {
        return "Auxiliary Computation";
    }

    @Override
    public String getDescription() {
        return "Finish auxiliary computation";
    }

    @Override
    public String getScriptCommandName() {
        return "aux-finish";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] { new FinishAuxiliaryMethodComputationMacro(),
                                  new FinishAuxiliaryLoopComputationMacro(),
                                  new FinishAuxiliaryBlockComputationMacro()};
    }
}