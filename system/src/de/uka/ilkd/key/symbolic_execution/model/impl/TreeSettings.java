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

package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

/**
 * The default implementation of {@link ITreeSettings}.
 * @author Martin Hentschel
 */
public class TreeSettings implements ITreeSettings {
   /**
    * {@code true} merge branch conditions which means that a branch condition never contains another branch condition
    * or {@code false} allow that branch conditions contains branch conditions.
    */
   private final boolean mergeBranchConditions;

   /**
    * {@code true} use unicode characters, {@code false} do not use unicode characters.
    */
   private final boolean useUnicode;
   
   /**
    * {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   private final boolean usePrettyPrinting;

   /**
    * Constructor.
    * @param mergeBranchConditions {@code true} merge branch conditions which means that a branch condition never contains another branch condition or {@code false} allow that branch conditions contains branch conditions.
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   public TreeSettings(boolean mergeBranchConditions, 
                       boolean useUnicode,
                       boolean usePrettyPrinting) {
      this.mergeBranchConditions = mergeBranchConditions;
      this.useUnicode = useUnicode;
      this.usePrettyPrinting = usePrettyPrinting;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isMergeBranchConditions() {
      return mergeBranchConditions;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isUseUnicode() {
      return useUnicode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isUsePrettyPrinting() {
      return usePrettyPrinting;
   }
}