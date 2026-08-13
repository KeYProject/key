/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Equality;

import org.key_project.logic.op.Function;
import org.key_project.prover.strategy.ArithTermFeatures;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

class JavaArithTermFeatures extends ArithTermFeatures {

    public JavaArithTermFeatures(IntegerLDT numbers) {
        super(numbers, Equality.EQUALS);
        C = numbers.getCharSymbol();

        jmod = numbers.getJModulo();
        jdiv = numbers.getJDivision();

        jmodF = op(jmod);
        jdivF = op(jdiv);

        charLiteral = op(C);

        notContainsDivMod = rec(any(), add(add(not(divF), not(modF)), add(not(jdivF), not(jmodF))));
    }


    final Function C;
    final Function jmod;
    final Function jdiv;

    final TermFeature jmodF;
    final TermFeature jdivF;

    final TermFeature charLiteral;
}
