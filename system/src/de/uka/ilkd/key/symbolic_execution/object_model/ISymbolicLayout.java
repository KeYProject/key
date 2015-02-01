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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.symbolic_execution.SymbolicLayoutExtractor;
import de.uka.ilkd.key.symbolic_execution.SymbolicLayoutReader;
import de.uka.ilkd.key.symbolic_execution.SymbolicLayoutWriter;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicLayout;

/**
 * <p>
 * This interface represents the root element of a symbolic memory layout.
 * </p>
 * <p>
 * A symbolic memory layout defines how a heap and stack looks like and which objects
 * are the same (equivalent classes). Such memory layouts can be created
 * automatically via a {@link SymbolicLayoutExtractor} and saved/loaded
 * via {@link SymbolicLayoutWriter}/{@link SymbolicLayoutReader}.
 * </p>
 * <p>
 * The default implementation is {@link SymbolicLayout}.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicLayoutExtractor
 * @see SymbolicLayoutWriter
 * @see SymbolicLayoutReader
 * @see SymbolicLayout
 */
public interface ISymbolicLayout extends ISymbolicElement {
   /**
    * Returns the equivalence classes. 
    * @return The equivalence classes.
    */
   public ImmutableList<ISymbolicEquivalenceClass> getEquivalenceClasses();
   
   /**
    * Returns the symbolic state.
    * @return the symbolic state.
    */
   public ISymbolicState getState();
   
   /**
    * Returns all available symbolic objects.
    * @return The available symbolic objects.
    */
   public ImmutableList<ISymbolicObject> getObjects();
}