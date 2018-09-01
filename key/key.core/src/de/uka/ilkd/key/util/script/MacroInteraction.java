package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Node;

/**
 * @author weigl
 */
public final class MacroInteraction extends Interaction {
    private final ProofMacro macro;
    private final PosInOccurrence pos;

    public MacroInteraction(Node node, ProofMacro macro, PosInOccurrence posInOcc) {
        super(node);
        this.macro = macro;
        this.pos = posInOcc;
    }

    @Override
    public String getProofScriptRepresentation(Services services) {
        return macro.getScriptCommandName() + ";";
    }

    public ProofMacro getMacro() {
        return macro;
    }

    public PosInOccurrence getPos() {
        return pos;
    }
}
