package de.uka.ilkd.key.rule.label;

import java.util.LinkedList;
import java.util.List;

import org.key_project.util.java.CollectionUtil;

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;

/**
 * The {@link TermLabelMerger} used to merge {@link FormulaTermLabel}s.
 * @author Martin Hentschel
 */
public class FormulaTermLabelMerger implements TermLabelMerger {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean mergeLabels(SequentFormula existingSF, 
                              Term existingTerm, 
                              TermLabel existingLabel, 
                              SequentFormula rejectedSF, 
                              Term rejectedTerm, 
                              TermLabel rejectedLabel, 
                              List<TermLabel> mergedLabels) {
      if (existingLabel != null) {
         FormulaTermLabel fExisting = (FormulaTermLabel) existingLabel;
         FormulaTermLabel fRejected = (FormulaTermLabel) rejectedLabel;
         // Compute new label
         List<String> newBeforeIds = new LinkedList<String>();
         CollectionUtil.addAll(newBeforeIds, fExisting.getBeforeIds());
         CollectionUtil.addAll(newBeforeIds, fRejected.getId());
         CollectionUtil.addAll(newBeforeIds, fRejected.getBeforeIds());
         FormulaTermLabel newLabel = new FormulaTermLabel(fExisting.getMajorId(), fExisting.getMinorId(), newBeforeIds);
         // Remove existing label
         mergedLabels.remove(existingLabel);
         // Add new label
         mergedLabels.add(newLabel);
         return true;
      }
      else {
         mergedLabels.add(rejectedLabel);
         return true;
      }
   }
}
