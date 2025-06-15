/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Equality;

import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

import org.jspecify.annotations.NonNull;

class ArithTermFeatures extends StaticFeatureCollection {

    public ArithTermFeatures(@NonNull IntegerLDT numbers) {
        Z = numbers.getNumberSymbol();
        C = numbers.getCharSymbol();

        add = numbers.getAdd();
        mul = numbers.getMul();
        mod = numbers.getMod();
        div = numbers.getDiv();
        jmod = numbers.getJModulo();
        jdiv = numbers.getJDivision();

        eq = Equality.EQUALS;
        leq = numbers.getLessOrEquals();
        geq = numbers.getGreaterOrEquals();

        intS = numbers.getNumberSymbol().sort();

        intF = extendsTrans(intS);

        addF = op(add);
        mulF = op(mul);
        modF = op(mod);
        divF = op(div);
        jmodF = op(jmod);
        jdivF = op(jdiv);

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

        charLiteral = op(C);

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
        notContainsDivMod = rec(any(), add(add(not(divF), not(modF)), add(not(jdivF), not(jmodF))));
    }

    final @NonNull Sort intS;

    final Function Z;
    final Function C;
    final Function add;
    final Function mul;
    final Function mod;
    final Function div;
    final Function jmod;
    final Function jdiv;

    final Operator eq;
    final Function leq;
    final Function geq;

    final @NonNull TermFeature intF;

    final @NonNull TermFeature addF;
    final @NonNull TermFeature mulF;
    final @NonNull TermFeature modF;
    final @NonNull TermFeature divF;
    final @NonNull TermFeature jmodF;
    final @NonNull TermFeature jdivF;

    final @NonNull TermFeature eqF;
    final @NonNull TermFeature leqF;
    final @NonNull TermFeature geqF;

    final @NonNull TermFeature constant;
    final @NonNull TermFeature atom;
    final @NonNull TermFeature linearMonomial;

    // left-associatively arranged monomials
    final @NonNull TermFeature monomial;
    // left-associatively arranged polynomials
    final @NonNull TermFeature polynomial;

    final @NonNull TermFeature literal;
    final @NonNull TermFeature posLiteral;
    final @NonNull TermFeature negLiteral;
    final @NonNull TermFeature nonNegLiteral;
    final @NonNull TermFeature nonPosLiteral;
    final @NonNull TermFeature zeroLiteral;
    final @NonNull TermFeature oneLiteral;
    final @NonNull TermFeature atLeastTwoLiteral;

    final @NonNull TermFeature charLiteral;

    final @NonNull TermFeature nonNegMonomial;
    final @NonNull TermFeature posMonomial;
    final @NonNull TermFeature negMonomial;
    final @NonNull TermFeature nonCoeffMonomial;
    final @NonNull TermFeature nonNegOrNonCoeffMonomial;
    final @NonNull TermFeature atLeastTwoCoeffMonomial;

    final @NonNull TermFeature intEquation;
    final @NonNull TermFeature linearEquation;
    final @NonNull TermFeature monomialEquation;
    final @NonNull TermFeature intInEquation;
    final @NonNull TermFeature linearInEquation;
    final @NonNull TermFeature intRelation;

    final @NonNull TermFeature notContainsProduct;
    final @NonNull TermFeature notContainsDivMod;

}
