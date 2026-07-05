/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import org.jspecify.annotations.NullMarked;

/**
 * Introduction rule for {@link OssLemmaGenerator}: at a top level formula that the one step
 * simplifier can simplify, it introduces the taclet capturing the aggregated simplification,
 * together with its soundness proof obligation.
 */
@NullMarked
public final class OssLemmaIntroductionRule extends LemmaIntroductionRule {

    public static final OssLemmaIntroductionRule INSTANCE = new OssLemmaIntroductionRule();

    private OssLemmaIntroductionRule() {
        super(OssLemmaGenerator.INSTANCE);
    }
}
