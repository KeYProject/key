package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * An annotated edge representing a chain of real proof nodes.
 *
 * @author Arne Keller
 */
public class AnnotatedShortenedEdge extends AnnotatedEdge {
    private Node initial;
    private Node last;

    public AnnotatedShortenedEdge(Node initial, Node last, boolean consumesInput) {
        super(last, consumesInput);
        this.initial = initial;
        this.last = last;
    }

    public String getEdgeLabel() {
        var sb = new StringBuilder();
        RuleApp ruleApp1 = initial.getAppliedRuleApp();
        if (ruleApp1 != null) {
            sb.append(ruleApp1.rule().displayName()).append("_").append(initial.serialNr());
            sb.append(" ... ");
        }
        RuleApp ruleApp2 = last.getAppliedRuleApp();
        if (ruleApp2 != null) {
            sb.append(ruleApp2.rule().displayName()).append("_").append(last.serialNr());
        }
        return sb.toString();
    }

    public Node getInitial() {
        return initial;
    }
}
