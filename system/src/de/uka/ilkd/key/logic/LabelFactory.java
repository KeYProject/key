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

package de.uka.ilkd.key.logic;

import java.util.List;

/**
 * Factory class for term labels
 * 
 * Attention: TermLabels used as patterns or construction labels are provided by the
 * label factory in package rule.label
 */
public class LabelFactory {
   public static ITermLabel createLabel(String name, List<String> parameters) throws UnknownLabelException {
      if (SymbolicExecutionTermLabel.NAME.toString().equals(name)) {
         if (parameters != null && parameters.size() == 1) {
            return new SymbolicExecutionTermLabel(Integer.valueOf(parameters.get(0)));
         }
         else {
            throw new IllegalArgumentException("Label " + SymbolicExecutionTermLabel.NAME + " requires exactly one Integer-Parameter with its ID.");
         }
      }
      else if (LoopBodyTermLabel.NAME.toString().equals(name)) {
         return LoopBodyTermLabel.INSTANCE;
      }
      else if (LoopInvariantNormalBehaviorTermLabel.NAME.toString().equals(name)) {
         return LoopInvariantNormalBehaviorTermLabel.INSTANCE;
      }
      else {
         throw new UnknownLabelException(name);
      }
   }
}