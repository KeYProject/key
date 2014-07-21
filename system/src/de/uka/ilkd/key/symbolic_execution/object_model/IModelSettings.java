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

package de.uka.ilkd.key.symbolic_execution.object_model;

/**
 * Provides the settings used to construct a symbolic object model.
 * @author Martin Hentschel
 */
public interface IModelSettings {
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
}