/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy;

import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

public interface IFormulaTermFeatures {
    TermFeature forF();

    TermFeature orF();

    TermFeature andF();

    TermFeature impF();

    TermFeature notF();

    TermFeature propJunctor();

    TermFeature ifThenElse();

    TermFeature notExecutable();

    TermFeature notContainsExecutable();

    TermFeature quantifiedFor();

    TermFeature quantifiedOr();

    TermFeature quantifiedAnd();

    TermFeature atom();

    TermFeature literal();

    TermFeature clause();

    TermFeature clauseSet();

    TermFeature quantifiedClauseSet();

    TermFeature pureLitConjDisj();

    TermFeature quantifiedPureLitConjDisj();

    TermFeature elemUpdate();

    TermFeature update();

    TermFeature program();

    TermFeature modalOperator();

    TermFeature cutAllowed();

    TermFeature cutAllowedBelowQuantifier();

    TermFeature cutPriority();
}
