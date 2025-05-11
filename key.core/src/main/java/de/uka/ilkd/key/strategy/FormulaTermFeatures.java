/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.strategy.termfeature.AtomTermFeature;
import de.uka.ilkd.key.strategy.termfeature.ContainsExecutableCodeTermFeature;
import de.uka.ilkd.key.strategy.termfeature.OperatorClassTF;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;
import org.jspecify.annotations.NonNull;

class FormulaTermFeatures extends StaticFeatureCollection {

    public FormulaTermFeatures(@NonNull ArithTermFeatures tf) {
        forF = extendsTrans(JavaDLTheory.FORMULA);
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
            or(tf.eqF, OperatorClassTF.create(JFunction.class),
                OperatorClassTF.create(ProgramVariable.class),
                OperatorClassTF.create(LogicVariable.class))); // XXX
        cutAllowedBelowQuantifier = add(not(propJunctor), notContainsExecutable);
        cutPriority = add(
            ifZero(tf.intInEquation, longTermConst(0),
                ifZero(tf.eqF, longTermConst(100), longTermConst(200))),
            rec(any(), longTermConst(1)));
        // directCutAllowed = add ( tf.intInEquation, notContainsQuery );

    }

    final @NonNull TermFeature forF;

    final @NonNull TermFeature orF;
    final @NonNull TermFeature andF;
    final @NonNull TermFeature impF;
    final @NonNull TermFeature notF;
    final @NonNull TermFeature propJunctor;
    final @NonNull TermFeature ifThenElse;
    final @NonNull TermFeature notExecutable;
    final @NonNull TermFeature notContainsExecutable;

    final @NonNull TermFeature quantifiedFor;
    final @NonNull TermFeature quantifiedOr;
    final @NonNull TermFeature quantifiedAnd;

    final @NonNull TermFeature atom;
    final @NonNull TermFeature literal;
    final @NonNull TermFeature clause;
    final @NonNull TermFeature clauseSet;
    final @NonNull TermFeature quantifiedClauseSet;

    final @NonNull TermFeature pureLitConjDisj;
    final @NonNull TermFeature quantifiedPureLitConjDisj;

    final @NonNull TermFeature elemUpdate;
    final @NonNull TermFeature update;
    final @NonNull TermFeature program;
    final @NonNull TermFeature modalOperator;

    final @NonNull TermFeature cutAllowed;
    final @NonNull TermFeature cutAllowedBelowQuantifier;
    final @NonNull TermFeature cutPriority;
}
