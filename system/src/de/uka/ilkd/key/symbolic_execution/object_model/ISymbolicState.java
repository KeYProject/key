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

import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicState;

/**
 * <p>
 * Represents the symbolic state of an {@link ISymbolicLayout}.
 * </p>
 * <p>
 * The default implementation is {@link SymbolicState}.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicState
 */
public interface ISymbolicState extends ISymbolicAssociationValueContainer {
   /**
    * Returns the name of this state.
    * @return The name of this state.
    */
   public String getName();
}