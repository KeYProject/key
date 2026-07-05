/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.lemma;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RewriteTaclet;

import org.key_project.logic.Name;
import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NullMarked;

/**
 * A generator that computes a specialized taclet capturing the effect of a programmatic
 * transformation at a given position. Instead of performing the transformation directly on the
 * proof (as {@link org.key_project.logic.op.TermTransformer term transformers} or many built-in
 * rules do), the transformation is packaged as a taclet so that
 * <ul>
 * <li>the performed step is inspectable as a declarative artifact,</li>
 * <li>its correctness can be established by a separate soundness proof registered in the same
 * proof environment, and</li>
 * <li>the taclet can be reused when the same transformation is required again.</li>
 * </ul>
 *
 * Implementations must obey the following contract:
 * <ul>
 * <li><b>Context-freeness:</b> the generated taclet must be sound in the empty context, i.e., its
 * validity must not depend on branch-local knowledge. Hypotheses required for soundness have to be
 * made explicit as {@code \assumes} clauses of the taclet.</li>
 * <li><b>Provability:</b> the taclet must lie in the fragment supported by the taclet soundness
 * proof obligation machinery (see
 * {@link de.uka.ilkd.key.taclettranslation.lemma.DefaultLemmaGenerator}): no variable conditions,
 * no metaconstructs, no modalities.</li>
 * <li><b>Determinism:</b> replaying the introducing rule application (same node, same sequent)
 * must regenerate an identical taclet, in particular the identical name. Purely content-derived
 * names are only sound if the content cannot contain proof-local symbols: formulas on different
 * branches can be equal in their printed form yet contain distinct program variable or skolem
 * constant instances sharing the same name. Generators for such content must additionally
 * qualify the name with a replay-stable introduction-point id (see
 * {@link de.uka.ilkd.key.proof.Node#getUniqueTacletId()}).</li>
 * </ul>
 */
@NullMarked
public interface LemmaTacletGenerator {

    /**
     * returns the unique name of this generator
     */
    Name name();

    /**
     * checks whether this generator can compute a lemma taclet for the term at the given position
     *
     * @param goal the current goal
     * @param pio the position of the term to be transformed
     * @return true iff {@link #generate(Goal, PosInOccurrence)} will succeed at the given position
     */
    boolean isApplicable(Goal goal, PosInOccurrence pio);

    /**
     * computes the lemma taclet for the term at the given position. The result must be
     * deterministic in the content of the term at the position (see the class-level contract).
     *
     * @param goal the current goal
     * @param pio the position of the term to be transformed
     * @return the generated taclet
     */
    RewriteTaclet generate(Goal goal, PosInOccurrence pio);
}
