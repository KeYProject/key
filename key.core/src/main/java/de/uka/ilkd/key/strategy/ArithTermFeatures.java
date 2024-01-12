/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.strategy.termfeature.ConstantTermFeature;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;

class ArithTermFeatures extends StaticFeatureCollection {

    public ArithTermFeatures(IntegerLDT numbers) {
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

        constant = ConstantTermFeature.INSTANCE;

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

    final Sort intS;

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

    final TermFeature intF;

    final TermFeature addF;
    final TermFeature mulF;
    final TermFeature modF;
    final TermFeature divF;
    final TermFeature jmodF;
    final TermFeature jdivF;

    final TermFeature eqF;
    final TermFeature leqF;
    final TermFeature geqF;

    final TermFeature constant;
    final TermFeature atom;
    final TermFeature linearMonomial;

    // left-associatively arranged monomials
    final TermFeature monomial;
    // left-associatively arranged polynomials
    final TermFeature polynomial;

    final TermFeature literal;
    final TermFeature posLiteral;
    final TermFeature negLiteral;
    final TermFeature nonNegLiteral;
    final TermFeature nonPosLiteral;
    final TermFeature zeroLiteral;
    final TermFeature oneLiteral;
    final TermFeature atLeastTwoLiteral;

    final TermFeature charLiteral;

    final TermFeature nonNegMonomial;
    final TermFeature posMonomial;
    final TermFeature negMonomial;
    final TermFeature nonCoeffMonomial;
    final TermFeature nonNegOrNonCoeffMonomial;
    final TermFeature atLeastTwoCoeffMonomial;

    final TermFeature intEquation;
    final TermFeature linearEquation;
    final TermFeature monomialEquation;
    final TermFeature intInEquation;
    final TermFeature linearInEquation;
    final TermFeature intRelation;

    final TermFeature notContainsProduct;
    final TermFeature notContainsDivMod;

}
