/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.prover.rules.MatchConditions;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.ArithLogicalExpression;
import org.key_project.rusty.ast.expr.LiteralExpression;
import org.key_project.rusty.ast.expr.PathExpression;
import org.key_project.rusty.ldt.LDT;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.logic.sort.ProgramSVSort;
import org.key_project.rusty.rule.inst.IllegalInstantiationException;
import org.key_project.rusty.rule.inst.SVInstantiations;

import org.jspecify.annotations.NonNull;

public class MatchProgramSVInstruction extends MatchSchemaVariableInstruction<@NonNull ProgramSV>
        implements MatchOperatorInstruction {

    public MatchProgramSVInstruction(ProgramSV sv) {
        super(sv);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Term instantiationCandidate,
            MatchConditions matchCond,
            LogicServices services) {
        final ProgramSVSort svSort = (ProgramSVSort) op.sort();

        if (svSort.canStandFor(instantiationCandidate)) {
            return addInstantiation(instantiationCandidate,
                matchCond, services);
        }

        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Operator instantiationCandidate,
            MatchConditions matchConditions,
            LogicServices services) {
        if (instantiationCandidate instanceof RustyProgramElement pe) {
            return match(pe, matchConditions, services);
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions matchConditions,
            LogicServices services) {
        MatchConditions result = match((Term) cursor.getCurrentNode(), matchConditions, services);
        if (result != null) {
            cursor.gotoNextSibling();
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(
            RustyProgramElement instantiationCandidate,
            MatchConditions matchCond,
            LogicServices services) {
        final ProgramSVSort svSort = (ProgramSVSort) op.sort();

        // TODO: will need execution context when we add functions (in the Rust programs)
        if (svSort.canStandFor(instantiationCandidate, (Services) services)) {
            return addInstantiation(instantiationCandidate, matchCond, (Services) services);
        }

        return null;
    }

    /**
     * tries to add the pair <tt>(this,pe)</tt> to the match conditions. If possible the resulting
     * match conditions are returned, otherwise <tt>null</tt>. Such an addition can fail, e.g. if
     * already a pair <tt>(this,x)</tt> exists where <tt>x!=pe</tt>
     */
    private MatchConditions addInstantiation(RustyProgramElement pe, MatchConditions matchCond,
            Services services) {

        final SVInstantiations instantiations =
            (SVInstantiations) matchCond.getInstantiations();
        final Object inMap = instantiations.getInstantiation(op);

        if (inMap == null) {
            try {
                return matchCond.setInstantiations(instantiations.add(op, pe, services));
            } catch (IllegalInstantiationException e) {

            }
        } else {
            Object peForCompare = pe;
            if (inMap instanceof Term) {
                try {
                    peForCompare = convertToLogicElement(pe, services);
                } catch (RuntimeException re) {
                    return null;
                }
            }
            if (inMap.equals(peForCompare)) {
                return matchCond;
            }
        }
        return null;
    }

    // TODO: Move to suitable class
    public static Term convertToLogicElement(RustyProgramElement pe, Services services) {
        var tb = services.getTermBuilder();
        if (pe instanceof ProgramVariable pv) {
            return tb.var(pv);
        }
        if (pe instanceof PathExpression(org.key_project.rusty.ast.Identifier var)) {
            return tb.var(services.getNamespaces().programVariables().lookup(var.name()));
        }
        if (pe instanceof LiteralExpression lit) {
            return convertLiteralExpression(lit, services);
        }
        if (pe instanceof ArithLogicalExpression ale) {
            return convertArithLogicalExpression(ale, services);
        }
        throw new IllegalArgumentException(
            "Unknown or not convertible ProgramElement " + pe + " of type "
                + pe.getClass());
    }

    // TODO: Generalize to all operators (once we have them)
    public static Term convertArithLogicalExpression(ArithLogicalExpression ale,
            Services services) {
        var tb = services.getTermBuilder();
        final var subs = new Term[] { convertToLogicElement(ale.left(), services),
            convertToLogicElement(ale.right(), services) };

        var op = ale.op();
        var responsibleLDT = getResponsibleLDT(op, subs, services);
        if (responsibleLDT != null) {
            return tb.func(responsibleLDT.getFuctionFor(op, services), subs);
        }
        throw new IllegalArgumentException(
            "could not handle" + " this operator: " + op);
    }

    public static LDT getResponsibleLDT(ArithLogicalExpression.Operator op, Term[] subs,
            Services services) {
        for (LDT ldt : services.getLDTs()) {
            if (ldt.isResponsible(op, subs, services)) {
                return ldt;
            }
        }
        return null;
    }

    public static Term convertLiteralExpression(LiteralExpression lit, Services services) {
        LDT ldt = services.getLDTs().get(lit.getLDTName());
        if (ldt != null) {
            return ldt.translateLiteral(lit, services);
        } else {
            return null;
        }
    }
}
