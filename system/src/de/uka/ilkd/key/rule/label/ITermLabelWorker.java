// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.label;

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UseOperationContractRule;

/**
 * <p>
 * An {@link ITermLabelWorker} defines for one concrete {@link ITermLabel}
 * how it is maintained during proof, more concrete when a {@link Rule} is applied.
 * </p>
 * <p>
 * Which {@link ITermLabelWorker} instances are available during proof is defined
 * by the {@link Profile} always available via {@code proof.env().getInitConfig().getProfile()}.
 * </p>
 * <p>
 * During proof the class {@link TermLabelWorkerManagement} is responsible to
 * use the available {@link ITermLabelWorker} to maintain {@link ITermLabel}s.
 * </p>
 * <p>
 * Instructions how to implement new term labels can be found in the
 * interface documentation of {@link ITermLabel}.
 * </p>
 * @author Martin Hentschel
 * @see TermLabelWorkerManagement
 * @see ITermLabel
 * @see Profile#getLabelInstantiators()
 */
public interface ITermLabelWorker {
   /**
    * This method is called before a new {@link Term} is created during proof
    * to compute the labels it will contain.
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param applicationTerm The {@link Term} in the previous {@link Sequent} defined by the {@link PosInOccurrence} which is rewritten.
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return The {@link ITermLabel}s to add to the new {@link Term} which should be created.
    */
   public List<ITermLabel> instantiateLabels(Term tacletTerm, 
                                             PosInOccurrence applicationPosInOccurrence,
                                             Term applicationTerm,
                                             Rule rule,
                                             Goal goal,
                                             Operator newTermOp, 
                                             ImmutableArray<Term> newTermSubs, 
                                             ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                             JavaBlock newTermJavaBlock);
   
   /**
    * This method is used to update the labels of the given {@link Term}.
    * It is called from build in rules (e.g. {@link UseOperationContractRule})
    * to update labels in {@link Goal}s of unmodified {@link Term}s by the rule itself.
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param termToUpdate The {@link Term} to update its labels.
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param newLabels This {@link List} defines the new {@link ITermLabel} and can be modified by this method.
    */
   public void updateLabels(Term tacletTerm, 
                            PosInOccurrence applicationPosInOccurrence,
                            Term termToUpdate,
                            Rule rule,
                            Goal goal,
                            List<ITermLabel> newLabels);

   /**
    * Returns the unique name of this {@link ITermLabelWorker} which should
    * be identical with the name of the label for which it is responsible.
    * @return The unique name of this {@link ITermLabelWorker}.
    */
   public String getName();
}