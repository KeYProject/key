package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Node;

public class AutoModeInteraction extends NodeInteraction {

    private ApplyStrategyInfo info;

    public AutoModeInteraction() {
    }

    public AutoModeInteraction(Node node, ApplyStrategyInfo info) {
        super(node);
        this.info = info;
    }

    @Override
    public String getProofScriptRepresentation(Services services) {
        StringBuilder sb = new StringBuilder("auto");

        sb.append("\n\t");
        sb.append(info);

        sb.append(";");
        return sb.toString();
    }

    public ApplyStrategyInfo getInfo() {
        return info;
    }
}
