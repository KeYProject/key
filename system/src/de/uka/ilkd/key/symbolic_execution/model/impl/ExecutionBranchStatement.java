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

import java.io.IOException;
import java.io.StringWriter;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.Switch;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionBranchStatement}.
 * @author Martin Hentschel
 */
public class ExecutionBranchStatement extends AbstractExecutionBlockStartNode<BranchStatement> implements IExecutionBranchStatement {
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionBranchStatement(ITreeSettings settings, 
                                   KeYMediator mediator, 
                                   Node proofNode) {
      super(settings, mediator, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      BranchStatement bs = getActiveStatement();
      try {
         if (bs instanceof If) {
            StringWriter sw = new StringWriter();
            PrettyPrinter sb = new PrettyPrinter(sw, true);
            sb.printIf((If)bs, false);
            return sw.toString();
         }
         else if (bs instanceof Switch) {
            StringWriter sw = new StringWriter();
            PrettyPrinter sb = new PrettyPrinter(sw, true);
            sb.printSwitch((Switch)bs, false);
            return sw.toString();
         }
         else {
            return bs.toString();
         }
      }
      catch (IOException e) {
         return bs.toString();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IExecutionConstraint[] lazyComputeConstraints() {
      return SymbolicExecutionUtil.createExecutionConstraints(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Branch Statement";
   }
}