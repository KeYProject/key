package de.uka.ilkd.key.logic;

/**
 * Factory class for term labels
 * 
 * Attention: TermLabels used as patterns or construction labels are provided by the
 * label factory in package rule.label
 */
public class LabelFactory {
   public static ITermLabel createLabel(String name) throws UnknownLabelException {
      if ("SE".equals(name)) {
         return SymbolicExecutionLabel.INSTANCE;
      }
      else {
         throw new UnknownLabelException(name);
      }
   }
}
