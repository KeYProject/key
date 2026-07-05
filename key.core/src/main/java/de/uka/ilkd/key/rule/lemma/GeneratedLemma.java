/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RewriteTaclet;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A taclet created by a {@link LemmaTacletGenerator} together with its soundness proof.
 *
 * @param taclet the generated taclet; within one proof there is exactly one taclet instance per
 *        lemma name (see {@link GeneratedLemmaRegistry})
 * @param soundnessProof the proof for the soundness proof obligation of the taclet, or
 *        {@code null} if the obligation could not be created
 */
@NullMarked
public record GeneratedLemma(RewriteTaclet taclet, @Nullable Proof soundnessProof) {
}
