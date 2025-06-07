/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.logic.JTerm;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 *
 * @author christoph
 */
public class InfFlowSpec {
    public static final InfFlowSpec EMPTY_INF_FLOW_SPEC = new InfFlowSpec();

    public final ImmutableList<JTerm> preExpressions;

    public final ImmutableList<JTerm> postExpressions;

    public final ImmutableList<JTerm> newObjects;


    public InfFlowSpec(final ImmutableList<JTerm> preExpressions,
            final ImmutableList<JTerm> postExpressions, final ImmutableList<JTerm> newObjects) {
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
    public InfFlowSpec map(UnaryOperator<JTerm> op) {
        return new InfFlowSpec(preExpressions.stream().map(op).collect(ImmutableList.collector()),
            postExpressions.stream().map(op).collect(ImmutableList.collector()),
            newObjects.stream().map(op).collect(ImmutableList.collector()));
    }

    private InfFlowSpec() {
        this.preExpressions = ImmutableSLList.nil();
        this.postExpressions = ImmutableSLList.nil();
        this.newObjects = ImmutableSLList.nil();
    }
}
