/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.op.sv.OperatorSV;
import org.key_project.prover.rules.instantiation.IllegalInstantiationException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

public abstract class MatchSchemaVariableInstruction<SV extends OperatorSV>
        extends Instruction<SV> {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(MatchSchemaVariableInstruction.class);

    protected MatchSchemaVariableInstruction(SV op) {
        super(op);
    }

    /**
     * Tries to add the pair <tt>(this,term)</tt> to the match conditions. If successful the
     * resulting conditions are returned, otherwise null. Failure is possible e.g. if this
     * schemavariable has been already matched to a term <tt>t2</tt> which is not unifiable with the
     * given term.
     */
    protected final MatchConditions addInstantiation(JTerm term, MatchConditions matchCond,
            LogicServices services) {

        if (op.isRigid() && !term.isRigid()) {
            return null;
        }

        final SVInstantiations inst = matchCond.getInstantiations();

        final JTerm t = inst.getTermInstantiation(op, inst.getExecutionContext(), services);
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
     * {@link ProgramElement} {@code instantiationCandidate} w.r.t. the given constraints by
     * {@link MatchConditions}
     *
     * @param instantiationCandidate the {@link ProgramElement} to be matched
     * @param mc the {@link MatchConditions} with additional constraints (e.g. previous matches of
     *        this instructions {@link org.key_project.logic.op.sv.SchemaVariable})
     * @param services the {@link Services}
     * @return {@code null} if no matches have been found or the new {@link MatchConditions} with
     *         the pair ({@link org.key_project.logic.op.sv.SchemaVariable}, {@link ProgramElement})
     *         added
     */
    public MatchConditions match(ProgramElement instantiationCandidate, MatchConditions mc,
            LogicServices services) {
        return null;
    }


}
