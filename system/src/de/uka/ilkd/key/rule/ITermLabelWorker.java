package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.gui.configuration.LabelSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;

/**
 * <p>
 * An {@link ITermLabelWorker} defines for one concrete {@link ITermLabel}
 * how it is maintained during proof, more concrete when a {@link Rule} is applied.
 * </p>
 * <p>
 * Which {@link ITermLabelWorker} are available during proof are defined
 * by the {@link LabelSettings} as part of the {@link ProofSettings}. This
 * means that they are also saved in *.proof files. 
 * </p>
 * <p>
 * During proof and for persistence the class {@link TermLabelWorkerManagement}
 * is responsible.
 * </p>
 * @author Martin Hentschel
 * @see TermLabelWorkerManagement
 * @see ITermLabel
 * @see LabelSettings
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
    * @return The {@link ITermLabel}s to add to the updated {@link Term}.
    */
   public List<ITermLabel> updateLabels(Term tacletTerm, 
                                        PosInOccurrence applicationPosInOccurrence,
                                        Term termToUpdate,
                                        Rule rule,
                                        Goal goal);

   /**
    * Returns the unique name of this {@link ITermLabelWorker} which should
    * be identical with the name of the label for which it is responsible.
    * @return The unique name of this {@link ITermLabelWorker}.
    */
   public String getName();
}
