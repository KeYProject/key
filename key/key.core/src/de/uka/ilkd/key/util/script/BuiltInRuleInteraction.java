package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.BuiltInRule;

public class BuiltInRuleInteraction extends Interaction {
    public final BuiltInRule rule;
    public final PosInOccurrence pos;

    public BuiltInRuleInteraction(Node node, BuiltInRule rule, PosInOccurrence pos) {
        super(node);
        this.rule = rule;
        this.pos = pos;
    }

    @Override
    public String getProofScriptRepresentation(Services services) {
        return rule.displayName() + ";";
    }


    public BuiltInRule getRule() {
        return rule;
    }

    public PosInOccurrence getPos() {
        return pos;
    }
}