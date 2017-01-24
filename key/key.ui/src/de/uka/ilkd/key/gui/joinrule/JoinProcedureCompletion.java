// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.joinrule;

import java.util.Collection;
import java.util.HashMap;
import java.util.function.Function;

import de.uka.ilkd.key.gui.joinrule.predicateabstraction.PredicateAbstractionCompletion;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.join.JoinProcedure;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstraction;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstractionFactory;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

/**
 * A completion class for join procedures. Certain procedures, such as
 * {@link JoinWithPredicateAbstraction}, may not be complete initially and need
 * additional input.
 *
 * @author Dominic Scheurer
 */
public abstract class JoinProcedureCompletion<C extends JoinProcedure> {

    /**
     * @return The default completion (identity mapping).
     */
    public static <T extends JoinProcedure> JoinProcedureCompletion<T> defaultCompletion() {
        return create(proc -> proc);
    }

    /**
     * Default constructor is hidden. Use {@link #create(Function)} instead.
     */
    protected JoinProcedureCompletion() {
    }

    public static <T extends JoinProcedure> JoinProcedureCompletion<T> create(
            final Function<T, T> completion) {
        return new JoinProcedureCompletion<T>() {
            @Override
            public T complete(
                    T proc,
                    Pair<Goal, PosInOccurrence> joinGoalPio,
                    Collection<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> partners) {
                return completion.apply(proc);
            }
        };
    }

    /**
     * Completes the given join procedure either automatically (if the procedure
     * is already complete) or by demanding input from the user in a GUI.
     *
     * @param proc
     *            {@link JoinProcedure} to complete.
     * @param joinGoalPio
     *            TODO
     * @param partners
     *            TODO
     * @return The completed {@link JoinProcedure}.
     */
    public abstract C complete(
            final C proc,
            final Pair<Goal, PosInOccurrence> joinGoalPio,
            final Collection<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> partners);

    /**
     * Returns the completion for the given join procedure class.
     * 
     * @return The requested completion.
     */
    public static JoinProcedureCompletion<? extends JoinProcedure> getCompletionForClass(
            Class<? extends JoinProcedure> cls) {
        if (cls.equals(JoinWithPredicateAbstractionFactory.class)) {
            return new PredicateAbstractionCompletion();
        }
        else {
            return defaultCompletion();
        }
    }

}
