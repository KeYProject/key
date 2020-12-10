// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.LightweightSyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Stores the given {@link Term}, after substitution of {@link SchemaVariable}s,
 * into the given {@link SchemaVariable} for later use in other conditions and
 * transformers.
 *
 * @author Dominic Steinhoefel
 */
public class StoreTermInCondition implements VariableCondition {
    private final SchemaVariable storeInSV;
    private final Term term;

    public StoreTermInCondition(SchemaVariable resultVarSV, Term term) {
        this.storeInSV = resultVarSV;
        this.term = term;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(storeInSV) != null) {
            return matchCond;
        }

        final LightweightSyntacticalReplaceVisitor replVisitor = //
                new LightweightSyntacticalReplaceVisitor(svInst, services);
        term.execPostOrder(replVisitor);
        final Term instantiatedTerm = replVisitor.getTerm();

        return matchCond.setInstantiations( //
                svInst.add(storeInSV, instantiatedTerm, services));
    }

    @Override
    public String toString() {
        return String.format( //
                "\\varcond (\\storeTermIn(%s, %s))", storeInSV, term);
    }

}
