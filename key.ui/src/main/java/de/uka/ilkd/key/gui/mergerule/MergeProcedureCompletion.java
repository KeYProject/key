/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.mergerule;

import java.util.Collection;
import java.util.function.Function;

import de.uka.ilkd.key.gui.mergerule.predicateabstraction.PredicateAbstractionCompletion;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstractionFactory;
import de.uka.ilkd.key.util.Pair;

/**
 * A completion class for merge procedures. Certain procedures, such as
 * {@link MergeWithPredicateAbstraction}, may not be complete initially and need additional input.
 *
 * @author Dominic Scheurer
 */
public abstract class MergeProcedureCompletion<C extends MergeProcedure> {

    /**
     * @return The default completion (identity mapping).
     */
    public static <T extends MergeProcedure> MergeProcedureCompletion<T> defaultCompletion() {
        return create(proc -> proc);
    }

    /**
     * Default constructor is hidden. Use {@link #create(Function)} instead.
     */
    protected MergeProcedureCompletion() {
    }

    public static <T extends MergeProcedure> MergeProcedureCompletion<T> create(
            final Function<T, T> completion) {
        return new MergeProcedureCompletion<>() {
            @Override
            public T complete(
                    T proc, Pair<Goal, PosInOccurrence> mergeGoalPio,
                    Collection<MergePartner> partners) {
                return completion.apply(proc);
            }
        };
    }

    /**
     * Completes the given merge procedure either automatically (if the procedure is already
     * complete) or by demanding input from the user in a GUI.
     *
     * @param proc {@link MergeProcedure} to complete.
     * @param mergeGoalPio The {@link Goal} and {@link PosInOccurrence} identifying the merge goal.
     * @param partners The {@link MergePartner}s chosen.
     * @return The completed {@link MergeProcedure}.
     */
    public abstract C complete(final C proc, final Pair<Goal, PosInOccurrence> mergeGoalPio,
            final Collection<MergePartner> partners);

    /**
     * Returns the completion for the given merge procedure class.
     *
     * @return The requested completion.
     */
    public static MergeProcedureCompletion<? extends MergeProcedure> getCompletionForClass(
            Class<? extends MergeProcedure> cls) {
        if (cls.equals(MergeWithPredicateAbstractionFactory.class)) {
            return new PredicateAbstractionCompletion();
        } else {
            return defaultCompletion();
        }
    }

}
