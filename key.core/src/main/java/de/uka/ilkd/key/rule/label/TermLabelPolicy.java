// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.label;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;

/**
 * <p>
 * A {@link TermLabelPolicy} is used by
 * {@link TermLabelManager#instantiateLabels(
 *     TermLabelState, Services, PosInOccurrence, Term, Term, Rule, Goal,
 *     Object, Term, Operator, ImmutableArray, ImmutableArray, JavaBlock)}
 * to decide for each {@link TermLabel} of an old {@link Term} if it
 * should be re-added to the new {@link Term} or not.
 * </p>
 * <p>
 * For more information about {@link TermLabel}s and how they are maintained
 * during prove read the documentation of interface {@link TermLabel}.
 * </p>
 * @author Martin Hentschel
 * @see TermLabel
 * @see TermLabelManager
 */
public interface TermLabelPolicy {
   /**
    * Decides to keep (add to term which will be created) or to
    * drop (do not add label to new term) the given {@link TermLabel}
    * provided by the application {@link Term}.
    * @param state The {@link TermLabelState} of the current rule application.
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten.
    * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied.
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param hint An optional hint passed from the active rule to describe the term which should be created.
    * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate the new {@link Term} for the new proof node or {@code null} in case of built in rules.
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @param newTermOriginalLabels The original {@link TermLabel}s.
    * @param label The {@link TermLabel} to decide if it should be kept or dropped.
    * @return The {@link TermLabel} to keep which might be a different one (e.g. with changed parameters) or {@code null} if the {@link TermLabel} should be dropped.
    */
   public TermLabel keepLabel(TermLabelState state,
                              Services services,
                              PosInOccurrence applicationPosInOccurrence,
                              Term applicationTerm,
                              Rule rule,
                              Goal goal,
                              Object hint,
                              Term tacletTerm,
                              Operator newTermOp,
                              ImmutableArray<Term> newTermSubs,
                              ImmutableArray<QuantifiableVariable> newTermBoundVars,
                              JavaBlock newTermJavaBlock,
                              ImmutableArray<TermLabel> newTermOriginalLabels,
                              TermLabel label);
}