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

package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.symbolic_execution.SymbolicConfigurationExtractor;
import de.uka.ilkd.key.symbolic_execution.SymbolicConfigurationReader;
import de.uka.ilkd.key.symbolic_execution.SymbolicConfigurationWriter;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicConfiguration;

/**
 * <p>
 * This interface represents the root element of a symbolic configuration.
 * </p>
 * <p>
 * A symbolic configuration defines how a heap and stack looks like and which objects
 * are the same (equivalent classes). Such configurations can be created
 * automatically via a {@link SymbolicConfigurationExtractor} and saved/loaded
 * via {@link SymbolicConfigurationWriter}/{@link SymbolicConfigurationReader}.
 * </p>
 * <p>
 * The default implementation is {@link SymbolicConfiguration}.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicConfigurationExtractor
 * @see SymbolicConfigurationWriter
 * @see SymbolicConfigurationReader
 * @see SymbolicConfiguration
 */
public interface ISymbolicConfiguration {
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