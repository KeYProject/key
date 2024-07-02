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

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionLoopStatement}.
 * @author Martin Hentschel
 */
public class ExecutionLoopStatement extends AbstractExecutionBlockStartNode<LoopStatement> implements IExecutionLoopStatement {
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionLoopStatement(ITreeSettings settings, 
                                 Node proofNode) {
      super(settings, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      LoopStatement ls = getActiveStatement();
      try {
         if (ls.getGuardExpression() != null) {
            if (ls instanceof While) {
               StringWriter sw = new StringWriter();
               PrettyPrinter sb = new PrettyPrinter(sw, true);
               sb.printWhile((While)ls, false);
               return sw.toString();
            }
            else if (ls instanceof For) {
               StringWriter sw = new StringWriter();
               PrettyPrinter sb = new PrettyPrinter(sw, true);
               sb.printFor((For)ls, false);
               return sw.toString();
            }
            else if (ls instanceof EnhancedFor) {
               StringWriter sw = new StringWriter();
               PrettyPrinter sb = new PrettyPrinter(sw, true);
               sb.printEnhancedFor((EnhancedFor)ls, false);
               return sw.toString();
            }
            else if (ls instanceof Do) {
               StringWriter sw = new StringWriter();
               PrettyPrinter sb = new PrettyPrinter(sw, true);
               sb.printDo((Do)ls, false);
               return sw.toString();
            }
            else {
               return ls.toString();
            }
         }
         else {
            return ls.toString();
         }
      }
      catch (IOException e) {
         return ls.toString();
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
      return "Loop Statement";
   }
}