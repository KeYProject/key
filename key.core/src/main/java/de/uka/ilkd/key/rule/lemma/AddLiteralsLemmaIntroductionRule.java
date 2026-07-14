/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import org.jspecify.annotations.NullMarked;

/**
 * Introduction rule for {@link AddLiteralsLemmaGenerator}: at a sum of two integer literals it
 * introduces the ground rewrite taclet folding the sum, together with its soundness proof
 * obligation.
 */
@NullMarked
public final class AddLiteralsLemmaIntroductionRule extends LemmaIntroductionRule {

    public static final AddLiteralsLemmaIntroductionRule INSTANCE =
        new AddLiteralsLemmaIntroductionRule();

    private AddLiteralsLemmaIntroductionRule() {
        super(AddLiteralsLemmaGenerator.INSTANCE);
    }
}
