package de.uka.ilkd.key.rule.label;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;

/**
 * <p>
 * A {@link TermLabelMerger} is used by
 * {@link TermLabelManager#mergeLabels(Services, de.uka.ilkd.key.logic.SequentChangeInfo)}
 * to merge {@link TermLabel}s in case a {@link SequentFormula} was 
 * rejected to be added to the resulting {@link Sequent}.
 * </p>
 * <p>
 * For more information about {@link TermLabel}s and how they are maintained
 * during prove read the documentation of interface {@link TermLabel}.
 * </p>
 * @author Martin Hentschel
 * @see TermLabel
 * @see TermLabelManager
 */
public interface TermLabelMerger {
   /**
    * Merges the existing and the rejected {@link TermLabel} by updating the merged {@link List}.
    * @param existingSF The existing {@link SequentFormula}.
    * @param existingTerm The {@link Term} of the existing {@link SequentFormula}.
    * @param existingLabel The existing {@link TermLabel} if available or {@code null} otherwise.
    * @param rejectedSF The rejected {@link SequentFormula}.
    * @param rejectedTerm The {@link Term} of the rejected {@link SequentFormula}.
    * @param rejectedLabel The rejected {@link TermLabel}.
    * @param mergedLabels The {@link List} with new {@link TermLabel}s which will be visible in the resulting {@link Sequent}.
    * @return {@code true} if the {@link List} of {@link TermLabel} was modified and {@code false} otherwise.
    */
   public boolean mergeLabels(SequentFormula existingSF, 
                              Term existingTerm, 
                              TermLabel existingLabel, 
                              SequentFormula rejectedSF, 
                              Term rejectedTerm, 
                              TermLabel rejectedLabel,
                              List<TermLabel> mergedLabels);
}
