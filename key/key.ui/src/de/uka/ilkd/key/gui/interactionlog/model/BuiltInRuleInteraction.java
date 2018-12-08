package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

public class BuiltInRuleInteraction extends NodeInteraction {
    public BuiltInRule rule;
    public PosInOccurrence pos;

    public BuiltInRuleInteraction() {
    }

    public BuiltInRuleInteraction(Node node, IBuiltInRuleApp app, BuiltInRule rule, PosInOccurrence pos) {
        super(node);
        this.rule = rule;
        this.pos = pos;
    }

    @Override
    public String getProofScriptRepresentation(Services services) {
        return rule.displayName() + ";";
    }

    @Override
    public String getMarkdownText() {
        StringBuilder sb = new StringBuilder();

        sb
            .append("------\n")
            .append("## BuiltInRuleInteraction ")
            .append(rule.name())
            .append("\n\n")
            .append("### PosInOccurence\n")
            .append("```\n")
            .append(pos)
            .append("\n```\n\n");

        return sb.toString();
    }


    public BuiltInRule getRule() {
        return rule;
    }

    public PosInOccurrence getPos() {
        return pos;
    }
}