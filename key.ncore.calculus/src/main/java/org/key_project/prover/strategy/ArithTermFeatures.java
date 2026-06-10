/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy;

import org.key_project.ldt.IIntLdt;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

public class ArithTermFeatures extends StaticFeatureCollection {
    final Sort intS;

    final Function Z;
    final Function add;
    final Function mul;
    final Function mod;
    final Function div;

    final public Operator eq;
    final Function leq;
    final Function geq;

    final public TermFeature intF;

    final TermFeature addF;
    final TermFeature mulF;
    final protected TermFeature modF;
    final protected TermFeature divF;

    final public TermFeature eqF;
    final TermFeature leqF;
    final TermFeature geqF;

    final TermFeature constant;
    final public TermFeature atom;
    final TermFeature linearMonomial;

    // left-associatively arranged monomials
    final TermFeature monomial;
    // left-associatively arranged polynomials
    final public TermFeature polynomial;

    final public TermFeature literal;
    final TermFeature posLiteral;
    final public TermFeature negLiteral;
    final public TermFeature nonNegLiteral;
    final TermFeature nonPosLiteral;
    final TermFeature zeroLiteral;
    final TermFeature oneLiteral;
    final TermFeature atLeastTwoLiteral;

    final TermFeature nonNegMonomial;
    final TermFeature posMonomial;
    final TermFeature negMonomial;
    final TermFeature nonCoeffMonomial;
    final TermFeature nonNegOrNonCoeffMonomial;
    final TermFeature atLeastTwoCoeffMonomial;

    final public TermFeature intEquation;
    final TermFeature linearEquation;
    final TermFeature monomialEquation;
    final public TermFeature intInEquation;
    final TermFeature linearInEquation;
    final TermFeature intRelation;

    final public TermFeature notContainsProduct;
    public TermFeature notContainsDivMod;

    public ArithTermFeatures(IIntLdt numbers, Operator eq) {
        Z = numbers.getNumberSymbol();

        add = numbers.getAdd();
        mul = numbers.getMul();
        mod = numbers.getMod();
        div = numbers.getDiv();

        this.eq = eq;
        leq = numbers.getLessOrEquals();
        geq = numbers.getGreaterOrEquals();

        intS = numbers.getNumberSymbol().sort();

        intF = extendsTrans(intS);

        addF = op(add);
        mulF = op(mul);
        modF = op(mod);
        divF = op(div);

        eqF = op(eq);
        geqF = op(geq);
        leqF = op(leq);

        literal = op(Z);
        negLiteral = opSub(Z, op(numbers.getNegativeNumberSign()));
        nonNegLiteral = opSub(Z, not(op(numbers.getNegativeNumberSign())));
        zeroLiteral =
            opSub(Z, opSub(numbers.getNumberLiteralFor(0), op(numbers.getNumberTerminator())));
        oneLiteral =
            opSub(Z, opSub(numbers.getNumberLiteralFor(1), op(numbers.getNumberTerminator())));
        nonPosLiteral = or(zeroLiteral, negLiteral);
        posLiteral = add(nonNegLiteral, not(zeroLiteral));
        atLeastTwoLiteral = add(posLiteral, not(oneLiteral));

        constant = constantTermFeature();

        atom = add(not(addF), not(mulF));
        linearMonomial = or(atom, opSub(mul, atom, literal));

        // left-associatively arranged monomials, literals are only allowed
        // as right-most term
        monomial = or(atom, opSub(mul,
            rec(mulF, or(opSub(mul, any(), not(mulF)), add(not(addF), not(literal)))), atom));

        // left-associatively arranged polynomials
        polynomial = rec(addF, or(opSub(add, any(), not(addF)), monomial));

        nonNegMonomial = add(monomial, or(not(mulF), sub(any(), not(negLiteral))));
        posMonomial = opSub(mul, monomial, posLiteral);
        negMonomial = opSub(mul, monomial, negLiteral);
        nonCoeffMonomial = add(monomial, or(not(mulF), sub(any(), not(literal))));
        nonNegOrNonCoeffMonomial = add(monomial, or(not(mulF), sub(any(), not(negLiteral))));
        atLeastTwoCoeffMonomial = opSub(mul, monomial, atLeastTwoLiteral);

        intEquation = opSub(eq, add(intF, nonNegMonomial), add(intF, polynomial));
        linearEquation = opSub(eq, linearMonomial, add(intF, polynomial));
        monomialEquation = opSub(eq, add(intF, nonNegMonomial), add(intF, monomial));
        intInEquation = add(or(leqF, geqF), sub(nonNegMonomial, polynomial));
        linearInEquation = add(or(leqF, geqF), sub(linearMonomial, polynomial));
        intRelation = add(or(leqF, geqF, eqF), sub(add(intF, nonNegMonomial), polynomial));

        notContainsProduct = rec(any(), ifZero(mulF, not(sub(not(literal), not(literal)))));
        notContainsDivMod = rec(any(), add(not(divF), not(modF)));
    }
}
