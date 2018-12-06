package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Node;

/**
 * @author weigl
 */
public final class MacroInteraction extends NodeInteraction {
    private ProofMacro macro;
    private PosInOccurrence pos;
    private ProofMacroFinishedInfo info;

    public MacroInteraction() {
    }

    public MacroInteraction(Node node, ProofMacro macro, PosInOccurrence posInOcc, ProofMacroFinishedInfo info) {
        super(node);
        this.macro = macro;
        this.pos = posInOcc;
        this.info = info;
    }

    @Override
    public String getProofScriptRepresentation(Services services) {
        StringBuilder sb = new StringBuilder(macro.getScriptCommandName());

        sb.append("\n\t");
        sb.append(info);

        sb.append(";");
        return sb.toString();
    }

    public ProofMacro getMacro() {
        return macro;
    }

    public PosInOccurrence getPos() {
        return pos;
    }

    public ProofMacroFinishedInfo getInfo() {
        return info;
    }
}
