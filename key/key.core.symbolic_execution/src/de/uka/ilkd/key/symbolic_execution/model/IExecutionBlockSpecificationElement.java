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

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockSpecificationElement;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionBlockSpecificationElement;

/**
 * <p>
 * A node in the symbolic execution tree which represents a use block/loop contract application.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionBlockSpecificationElement} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionBlockSpecificationElement
 */
public interface IExecutionBlockSpecificationElement extends IExecutionNode<SourceElement> {
   /**
    * Returns the applied {@link BlockSpecificationElement}.
    * @return The applied {@link BlockSpecificationElement}.
    */
   public BlockSpecificationElement getContract();
   
   /**
    * Returns the {@link StatementBlock} at which the {@link BlockContract} is applied.
    * @return The {@link StatementBlock} at which the {@link BlockContract} is applied.
    */
   public StatementBlock getBlock();
   
   /**
    * Checks if the precondition is complied.
    * @return {@code true} precondition complied, {@code false} precondition not complied.
    */
   public boolean isPreconditionComplied(); 
}