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

    public final ImmutableList<Term> seperates;

    public final ImmutableList<Term> declassifies;

    public final ImmutableList<Term> erases;

    public final ImmutableList<Term> newObjects;


    public InfFlowSpec(final ImmutableList<Term> seperates,
                       final ImmutableList<Term> declassifies,
                       final ImmutableList<Term> erases,
                       final ImmutableList<Term> newObjects) {
        this.seperates = seperates;
        this.declassifies = declassifies;
        this.erases = erases;
        this.newObjects = newObjects;
    }

    private InfFlowSpec() {
        this.seperates = ImmutableSLList.<Term>nil();
        this.declassifies = ImmutableSLList.<Term>nil();
        this.erases = ImmutableSLList.<Term>nil();
        this.newObjects = ImmutableSLList.<Term>nil();
    }
}
