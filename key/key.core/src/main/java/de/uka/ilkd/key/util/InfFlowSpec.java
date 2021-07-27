package de.uka.ilkd.key.util;

import java.util.function.UnaryOperator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Term;


/**
 *
 * @author christoph
 */
public class InfFlowSpec {
    public static final InfFlowSpec EMPTY_INF_FLOW_SPEC = new InfFlowSpec();

    public final ImmutableList<Term> preExpressions;

    public final ImmutableList<Term> postExpressions;

    public final ImmutableList<Term> newObjects;


    public InfFlowSpec(final ImmutableList<Term> preExpressions,
                       final ImmutableList<Term> postExpressions,
                       final ImmutableList<Term> newObjects) {
        this.preExpressions = preExpressions;
        this.postExpressions = postExpressions;
        this.newObjects = newObjects;
    }

    /**
     * Applies a unary operator to every list of terms in this InfFlow specification element.
     *
     * @param op the operator to apply.
     * @return this InfFlow specification element with the operator applied.
     */
    public InfFlowSpec map(UnaryOperator<Term> op) {
        return new InfFlowSpec(
                preExpressions.stream().map(op).collect(ImmutableList.collector()),
                postExpressions.stream().map(op).collect(ImmutableList.collector()),
                newObjects.stream().map(op).collect(ImmutableList.collector()));
    }

    private InfFlowSpec() {
        this.preExpressions = ImmutableSLList.<Term>nil();
        this.postExpressions = ImmutableSLList.<Term>nil();
        this.newObjects = ImmutableSLList.<Term>nil();
    }
}
