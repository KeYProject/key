// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.join.procedures;

import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.getNewSkolemConstantForPrefix;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.rule.join.JoinProcedure;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * Rule that joins two sequents based on "total" weakening: Replacement of
 * symbolic state by an update setting every program variable to a fresh Skolem
 * constant, if the respective program variable does not evaluate to the same
 * value in both states - in this case, the original value is preserved (->
 * idempotency).
 * 
 * @author Dominic Scheurer
 */
public class JoinWeaken extends JoinProcedure {

    private static JoinWeaken INSTANCE = null;

    public static JoinWeaken instance() {
        if (INSTANCE == null) {
            INSTANCE = new JoinWeaken();
        }
        return INSTANCE;
    }

    private static final String DISPLAY_NAME = "JoinByFullAnonymization";

    @Override
    public Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>> joinValuesInStates(
            Term v, SymbolicExecutionState state1,
            Term valueInState1, SymbolicExecutionState state2,
            Term valueInState2, Services services) {

        final TermBuilder tb = services.getTermBuilder();

        final Function newSkolemConstant = getNewSkolemConstantForPrefix(v
                .op().name().toString(), v.sort(), services);
        ImmutableSet<Name> newNames = DefaultImmutableSet.nil();
        newNames = newNames.add(newSkolemConstant.name());

        return new Triple<ImmutableSet<Term>, Term, ImmutableSet<Name>>(
                DefaultImmutableSet.<Term> nil(), tb.func(newSkolemConstant),
                newNames);

    }

    @Override
    public boolean requiresDistinguishablePathConditions() {
        return false;
    }

    @Override
    public String toString() {
        return DISPLAY_NAME;
    }
}
