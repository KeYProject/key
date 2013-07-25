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

package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionLoopInvariant;

/**
 * <p>
 * A node in the symbolic execution tree which represents a loop invariant application.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionLoopInvariant} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionLoopInvariant
 */
public interface IExecutionLoopInvariant extends IExecutionStateNode<SourceElement> {
   /**
    * Returns the used {@link LoopInvariant}.
    * @return The used {@link LoopInvariant}.
    */
   public LoopInvariant getLoopInvariant();
   
   /**
    * Returns the loop statement which is simulated by its loop invariant.
    * @return The loop statement which is simulated by its loop invariant.
    */
   public While getLoopStatement();
   
   /**
    * Checks if the loop invariant is initially valid.
    * @return {@code true} initially valid, {@code false} initially invalid.
    */
   public boolean isInitiallyValid();
}