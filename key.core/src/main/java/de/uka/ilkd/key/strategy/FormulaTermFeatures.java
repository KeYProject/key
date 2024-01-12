/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.strategy.termfeature.AtomTermFeature;
import de.uka.ilkd.key.strategy.termfeature.ContainsExecutableCodeTermFeature;
import de.uka.ilkd.key.strategy.termfeature.OperatorClassTF;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

class FormulaTermFeatures extends StaticFeatureCollection {

    public FormulaTermFeatures(ArithTermFeatures tf) {
        forF = extendsTrans(Sort.FORMULA);
        orF = op(Junctor.OR);
        andF = op(Junctor.AND);
        impF = op(Junctor.IMP);
        notF = op(Junctor.NOT);
        ifThenElse = OperatorClassTF.create(IfThenElse.class);

        atom = AtomTermFeature.INSTANCE;
        propJunctor = or(OperatorClassTF.create(Junctor.class), op(Equality.EQV));
        literal = or(atom, opSub(Junctor.NOT, atom));

        // left-associatively arranged clauses
        clause = rec(orF, or(opSub(Junctor.OR, any(), not(orF)), literal));

        // left-associatively arranged sets of clauses
        clauseSet = rec(andF, or(opSub(Junctor.AND, any(), not(andF)), clause));

        quantifiedFor = or(op(Quantifier.ALL), op(Quantifier.EX));
        quantifiedClauseSet = rec(quantifiedFor, or(quantifiedFor, clauseSet));

        quantifiedAnd = rec(quantifiedFor, or(quantifiedFor, andF));
        quantifiedOr = rec(quantifiedFor, or(quantifiedFor, orF));

        // conjunction or disjunction of literals, without and-or
        // alternation
        pureLitConjDisj = or(rec(andF, or(andF, literal)), rec(orF, or(orF, literal)));
        quantifiedPureLitConjDisj = rec(quantifiedFor, or(quantifiedFor, pureLitConjDisj));

        elemUpdate = OperatorClassTF.create(ElementaryUpdate.class);
        update = OperatorClassTF.create(UpdateApplication.class);
        program = OperatorClassTF.create(Modality.class);
        modalOperator = or(update, program);

        // directCutAllowed = add ( atom, not ( modalOperator ) );
        notExecutable = not(program);

        notContainsExecutable = not(ContainsExecutableCodeTermFeature.PROGRAMS);

        cutAllowed = add(notContainsExecutable, tf.notContainsProduct,
            or(tf.eqF, OperatorClassTF.create(Function.class),
                OperatorClassTF.create(ParsableVariable.class))); // XXX
        cutAllowedBelowQuantifier = add(not(propJunctor), notContainsExecutable);
        cutPriority = add(
            ifZero(tf.intInEquation, longTermConst(0),
                ifZero(tf.eqF, longTermConst(100), longTermConst(200))),
            rec(any(), longTermConst(1)));
        // directCutAllowed = add ( tf.intInEquation, notContainsQuery );

    }

    final TermFeature forF;

    final TermFeature orF;
    final TermFeature andF;
    final TermFeature impF;
    final TermFeature notF;
    final TermFeature propJunctor;
    final TermFeature ifThenElse;
    final TermFeature notExecutable;
    final TermFeature notContainsExecutable;

    final TermFeature quantifiedFor;
    final TermFeature quantifiedOr;
    final TermFeature quantifiedAnd;

    final TermFeature atom;
    final TermFeature literal;
    final TermFeature clause;
    final TermFeature clauseSet;
    final TermFeature quantifiedClauseSet;

    final TermFeature pureLitConjDisj;
    final TermFeature quantifiedPureLitConjDisj;

    final TermFeature elemUpdate;
    final TermFeature update;
    final TermFeature program;
    final TermFeature modalOperator;

    final TermFeature cutAllowed;
    final TermFeature cutAllowedBelowQuantifier;
    final TermFeature cutPriority;
}
