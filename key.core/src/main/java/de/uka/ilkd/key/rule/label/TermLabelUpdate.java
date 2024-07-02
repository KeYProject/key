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

import java.util.Set;

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
import de.uka.ilkd.key.rule.RuleApp;

/**
 * <p>
 * A {@link TermLabelUpdate} is used by
 * {@link TermLabelManager#instantiateLabels(
 *     TermLabelState, Services, PosInOccurrence, Term, Term, Rule, Goal,
 *     Object, Term, Operator, ImmutableArray, ImmutableArray, JavaBlock)}
 * to add or remove maintained {@link TermLabel}s which will be added to the new {@link Term}.
 * </p>
 * <p>
 * For more information about {@link TermLabel}s and how they are maintained
 * during prove read the documentation of interface {@link TermLabel}.
 * </p>
 * @author Martin Hentschel
 * @see TermLabel
 * @see TermLabelManager
 */
public interface TermLabelUpdate extends RuleSpecificTask {
    /**
     * This method can freely add, remove or sort the given {@link TermLabel}
     * which will be added to the new {@link Term}.
     * @param state The {@link TermLabelState} of the current rule application.
     * return {@code true} keep {@link TermLabel} and add it to the new {@link Term}.
     *     {@code false} drop {@link TermLabel} and do not need it to the new {@link Term}.
     * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten.
     * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the previous {@link Sequent}.
     * @param modalityTerm The optional modality {@link Term}.
     * @param rule The {@link Rule} which is applied.
     * @param ruleApp The {@link RuleApp} which is currently performed.
     * @param hint An optional hint passed from the active rule to describe the term which should be created.
     * @param tacletTerm The optional {@link Term} in the taclet which is responsible to instantiate the new {@link Term} for the new proof node or {@code null} in case of built in rules.
     * @param newTermOp The new {@link Operator} of the {@link Term} to create.
     * @param newTermSubs The optional children of the {@link Term} to create.
     * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
     * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
     * @param labels The {@link Set} of {@link TermLabel}s to modify.
     */
    public void updateLabels(TermLabelState state,
            Services services,
            PosInOccurrence applicationPosInOccurrence,
            Term applicationTerm,
            Term modalityTerm,
            Rule rule,
            RuleApp ruleApp,
            Object hint,
            Term tacletTerm,
            Operator newTermOp,
            ImmutableArray<Term> newTermSubs,
            ImmutableArray<QuantifiableVariable> newTermBoundVars,
            JavaBlock newTermJavaBlock,
            Set<TermLabel> labels);
}