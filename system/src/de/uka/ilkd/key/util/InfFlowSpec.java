/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.util;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
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

    private InfFlowSpec() {
        this.preExpressions = ImmutableSLList.<Term>nil();
        this.postExpressions = ImmutableSLList.<Term>nil();
        this.newObjects = ImmutableSLList.<Term>nil();
    }
}
