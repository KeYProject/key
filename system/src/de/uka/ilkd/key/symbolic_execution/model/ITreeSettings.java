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

package de.uka.ilkd.key.symbolic_execution.model;

/**
 * Provides the settings used to construct the symbolic execution tree.
 * @author Martin Hentschel
 */
public interface ITreeSettings {
   /**
    * Checks if multiple branch conditions are merged or not.
    * @return {@code true} merge branch conditions which means that a branch condition never contains another branch condition
    * or {@code false} allow that branch conditions contains branch conditions.
    */
   public boolean isMergeBranchConditions();
   
   /**
    * Checks if unicode characters are used.
    * @return {@code true} use unicode characters, {@code false} do not use unicode characters.
    */
   public boolean isUseUnicode();

   /**
    * Checks if pretty printing is used or not.
    * @return {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   public boolean isUsePrettyPrinting();
   
   /**
    * Checks how variables are computed.
    * @return {@code true} {@link IExecutionVariable} are only computed from updates, {@code false} {@link IExecutionVariable}s are computed according to the type structure of the visible memory.
    */
   public boolean isVariablesAreOnlyComputedFromUpdates();
}