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

import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionStartNode;

/**
 * <p>
 * The start node of a symbolic execution tree.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionStartNode} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionStartNode
 */
public interface IExecutionStartNode extends IExecutionNode {
   /**
    * The default name of a start node.
    */
   public static final String DEFAULT_START_NODE_NAME = INTERNAL_NODE_NAME_START + "start" + INTERNAL_NODE_NAME_END;
}