/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.op.sv.OperatorSV;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.inst.IllegalInstantiationException;
import org.key_project.rusty.rule.inst.SVInstantiations;

import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.key_project.rusty.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

public abstract class MatchSchemaVariableInstruction<SV extends @NonNull OperatorSV>
        extends Instruction<SV> {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(MatchSchemaVariableInstruction.class);

    public MatchSchemaVariableInstruction(SV op) {
        super(op);
    }

    /**
     * Tries to add the pair <tt>(this,term)</tt> to the match conditions. If successful the
     * resulting conditions are returned, otherwise null. Failure is possible e.g. if this
     * schemavariable has been already matched to a term <tt>t2</tt> which is not unifiable with the
     * given term.
     */
    protected final MatchConditions addInstantiation(Term term, MatchConditions matchCond,
            Services services) {
        if (op.isRigid() && !term.isRigid()) {
            return null;
        }

        final SVInstantiations inst = matchCond.getInstantiations();

        final Term t = inst.getTermInstantiation(op, services);
        if (t != null) {
            if (!RENAMING_TERM_PROPERTY.equalsModThisProperty(t, term)) {
                return null;
            } else {
                return matchCond;
            }
        }

        try {
            return matchCond.setInstantiations(inst.add(op, term, services));
        } catch (IllegalInstantiationException e) {
            return null;
        }
    }

    /**
     * tries to match the schema variable of this instruction with the specified
     * {@link RustyProgramElement} {@code instantiationCandidate} w.r.t. the given constraints by
     * {@link MatchConditions}
     *
     * @param instantiationCandidate the {@link RustyProgramElement} to be matched
     * @param mc the {@link MatchConditions} with additional constraints (e.g. previous matches of
     *        this instructions {@link SchemaVariable})
     * @param services the {@link Services}
     * @return {@code null} if no matches have been found or the new {@link MatchConditions} with
     *         the pair ({@link SchemaVariable}, {@link RustyProgramElement}) added
     */
    public MatchConditions match(RustyProgramElement instantiationCandidate, MatchConditions mc,
            Services services) {
        return null;
    }
}
