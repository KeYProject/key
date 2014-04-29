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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicElement;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Default implementation of {@link ISymbolicElement}.
 * @author Martin Hentschel
 */
public abstract class AbstractElement implements ISymbolicElement {
   /**
    * The {@link IModelSettings} to use.
    */
   private final IModelSettings settings;

   /**
    * Constructor.
    * @param settings The {@link IModelSettings} to use.
    */
   public AbstractElement(IModelSettings settings) {
      this.settings = settings;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IModelSettings getSettings() {
      return settings;
   }

   /**
    * Converts the given {@link Term} into a {@link String} respecting {@link #isUsePretty()}.
    * @param term The {@link Term} to convert.
    * @param services The {@link Services} to use.
    * @return The {@link String} representation of the given {@link Term}.
    */
   protected String formatTerm(Term term, Services services) {
      return SymbolicExecutionUtil.formatTerm(term, services, settings.isUsePrettyPrinting());
   }
}