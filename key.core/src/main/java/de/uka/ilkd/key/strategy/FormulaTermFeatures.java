/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.strategy.termfeature.AtomTermFeature;
import de.uka.ilkd.key.strategy.termfeature.ContainsExecutableCodeTermFeature;

import org.key_project.logic.op.Function;
import org.key_project.prover.strategy.IFormulaTermFeatures;
import org.key_project.prover.strategy.costbased.termfeature.OperatorClassTF;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

class FormulaTermFeatures extends StaticFeatureCollection implements IFormulaTermFeatures {

    public FormulaTermFeatures(JavaArithTermFeatures tf) {
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
        program = OperatorClassTF.create(JModality.class);
        modalOperator = or(update, program);

        // directCutAllowed = add ( atom, not ( modalOperator ) );
        notExecutable = not(program);

        notContainsExecutable = not(ContainsExecutableCodeTermFeature.PROGRAMS);

        cutAllowed = add(notContainsExecutable, tf.notContainsProduct,
            or(tf.eqF, OperatorClassTF.create(Function.class),
                OperatorClassTF.create(ProgramVariable.class),
                OperatorClassTF.create(LogicVariable.class))); // XXX
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

    @Override
    public TermFeature forF() {
        return forF;
    }

    @Override
    public TermFeature orF() {
        return orF;
    }

    @Override
    public TermFeature andF() {
        return andF;
    }

    @Override
    public TermFeature impF() {
        return impF;
    }

    @Override
    public TermFeature notF() {
        return notF;
    }

    @Override
    public TermFeature propJunctor() {
        return propJunctor;
    }

    @Override
    public TermFeature ifThenElse() {
        return ifThenElse;
    }

    @Override
    public TermFeature notExecutable() {
        return notExecutable;
    }

    @Override
    public TermFeature notContainsExecutable() {
        return notContainsExecutable;
    }

    @Override
    public TermFeature quantifiedFor() {
        return quantifiedFor;
    }

    @Override
    public TermFeature quantifiedOr() {
        return quantifiedOr;
    }

    @Override
    public TermFeature quantifiedAnd() {
        return quantifiedAnd;
    }

    @Override
    public TermFeature atom() {
        return atom;
    }

    @Override
    public TermFeature literal() {
        return literal;
    }

    @Override
    public TermFeature clause() {
        return clause;
    }

    @Override
    public TermFeature clauseSet() {
        return clauseSet;
    }

    @Override
    public TermFeature quantifiedClauseSet() {
        return quantifiedClauseSet;
    }

    @Override
    public TermFeature pureLitConjDisj() {
        return pureLitConjDisj;
    }

    @Override
    public TermFeature quantifiedPureLitConjDisj() {
        return quantifiedPureLitConjDisj;
    }

    @Override
    public TermFeature elemUpdate() {
        return elemUpdate;
    }

    @Override
    public TermFeature update() {
        return update;
    }

    @Override
    public TermFeature program() {
        return program;
    }

    @Override
    public TermFeature modalOperator() {
        return modalOperator;
    }

    @Override
    public TermFeature cutAllowed() {
        return cutAllowed;
    }

    @Override
    public TermFeature cutAllowedBelowQuantifier() {
        return cutAllowedBelowQuantifier;
    }

    @Override
    public TermFeature cutPriority() {
        return cutPriority;
    }
}
