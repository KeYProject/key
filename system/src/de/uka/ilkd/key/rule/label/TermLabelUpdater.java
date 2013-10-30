package de.uka.ilkd.key.rule.label;

import java.util.List;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.UseOperationContractRule;

public interface TermLabelUpdater {
   public boolean isUpdateRequired(Term tacletTerm, 
                                   PosInOccurrence applicationPosInOccurrence, 
                                   Rule rule,
                                   Goal goal);
   
   /**
    * This method is used to update the labels of the given {@link Term}.
    * It is called from build in rules (e.g. {@link UseOperationContractRule})
    * to update labels in {@link Goal}s of unmodified {@link Term}s by the rule itself.
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param termToUpdate The {@link Term} to update its labels.
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param newLabels This {@link List} defines the new {@link TermLabel} and can be modified by this method.
    */
   public void updateLabels(Term tacletTerm, 
                            PosInOccurrence applicationPosInOccurrence,
                            Term termToUpdate,
                            Rule rule,
                            Goal goal,
                            List<TermLabel> newLabels);
}
