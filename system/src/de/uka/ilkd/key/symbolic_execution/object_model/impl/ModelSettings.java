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

package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;

/**
 * Default implementation of {@link IModelSettings}.
 * @author Martin Hentschel
 */
public class ModelSettings implements IModelSettings {
   /**
    * {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   private final boolean usePrettyPrinting;

   /**
    * Constructor.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   public ModelSettings(boolean usePrettyPrinting) {
      this.usePrettyPrinting = usePrettyPrinting;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isUsePrettyPrinting() {
      return usePrettyPrinting;
   }
}