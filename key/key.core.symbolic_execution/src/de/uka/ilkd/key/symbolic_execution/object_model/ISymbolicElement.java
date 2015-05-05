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
 * Defines the basic methods and properties each element in an
 * symbolic object model has to have.
 * @author Martin Hentschel
 */
public interface ISymbolicElement {
   /**
    * Returns the {@link IModelSettings} to use.
    * @return The {@link IModelSettings} to use.
    */
   public IModelSettings getSettings();
}