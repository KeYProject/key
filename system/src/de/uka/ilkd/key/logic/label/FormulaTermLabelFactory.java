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

package de.uka.ilkd.key.logic.label;

import java.util.List;

/**
 * A factory for creating {@link FormulaTermLabel} objects.
 */
public class FormulaTermLabelFactory implements TermLabelFactory<FormulaTermLabel> {
   /**
    * {@inheritDoc}
    * 
    * <p>
    * This method accepts single arguments which can be parsed as an integer.
    */
   @Override
   public FormulaTermLabel parseInstance(List<String> parameters) throws TermLabelException {
      if (parameters != null && parameters.size() == 1) {
         return new FormulaTermLabel(parameters.get(0));
      }
      else if (parameters != null && parameters.size() == 2) {
         return new FormulaTermLabel(parameters.get(0), parameters.get(1));
      }
      else {
         throw new TermLabelException("Label " + FormulaTermLabel.NAME + " requires the unique ID as first parameter and an optional by semicolon separated list of parent IDs as second parameter.");
      }
   }   
}