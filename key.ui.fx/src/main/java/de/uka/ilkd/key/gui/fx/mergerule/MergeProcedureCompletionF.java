/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.mergerule;

import java.util.Collection;
import java.util.function.Function;

import de.uka.ilkd.key.gui.fx.mergerule.predicateabstraction.PredicateAbstractionCompletionF;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.merge.MergePartner;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstractionFactory;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.Pair;

/**
 * A completion class for merge procedures. Certain procedures, such as
 * {@link MergeWithPredicateAbstraction}, may not be complete initially and need additional input.
 * <p>
 * Port of the Swing {@code de.uka.ilkd.key.gui.mergerule.MergeProcedureCompletion} (key.ui, pure
 * logic, unchanged).
 *
 * @author Dominic Scheurer (original Swing class)
 */
public abstract class MergeProcedureCompletionF<C extends MergeProcedure> {

    /**
     * @return The default completion (identity mapping).
     */
    public static <T extends MergeProcedure> MergeProcedureCompletionF<T> defaultCompletion() {
        return create(proc -> proc);
    }

    /**
     * Default constructor is hidden. Use {@link #create(Function)} instead.
     */
    protected MergeProcedureCompletionF() {
    }

    /**
     * Creates a completion that applies the given function to the procedure.
     *
     * @param completion the function to apply
     * @param <T> the concrete procedure type
     * @return a completion applying the given function
     */
    public static <T extends MergeProcedure> MergeProcedureCompletionF<T> create(
            final Function<T, T> completion) {
        return new MergeProcedureCompletionF<>() {
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
    public abstract C complete(final C proc,
            final Pair<Goal, PosInOccurrence> mergeGoalPio,
            final Collection<MergePartner> partners);

    /**
     * Returns the completion for the given merge procedure class.
     *
     * @param cls the procedure class
     * @return The requested completion.
     */
    public static MergeProcedureCompletionF<? extends MergeProcedure> getCompletionForClass(
            Class<? extends MergeProcedure> cls) {
        if (cls.equals(MergeWithPredicateAbstractionFactory.class)) {
            return new PredicateAbstractionCompletionF();
        } else {
            return defaultCompletion();
        }
    }

}
