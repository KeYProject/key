/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.core.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.ASTNode;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.sed.key.core.model.KeYBranchCondition;
import org.key_project.sed.key.core.model.KeYBranchStatement;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.model.KeYExceptionalTermination;
import org.key_project.sed.key.core.model.KeYLoopBodyTermination;
import org.key_project.sed.key.core.model.KeYLoopCondition;
import org.key_project.sed.key.core.model.KeYLoopInvariant;
import org.key_project.sed.key.core.model.KeYLoopStatement;
import org.key_project.sed.key.core.model.KeYMethodCall;
import org.key_project.sed.key.core.model.KeYMethodContract;
import org.key_project.sed.key.core.model.KeYMethodReturn;
import org.key_project.sed.key.core.model.KeYStatement;
import org.key_project.sed.key.core.model.KeYTermination;
import org.key_project.sed.key.core.model.KeYThread;
import org.key_project.sed.key.core.model.KeYVariable;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination.TerminationKind;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;

/**
 * Provides utility methods which are used by {@link IKeYSEDDebugNode}
 * implementations to compute their content and child {@link IKeYSEDDebugNode}s.
 * @author Martin Hentschel
 */
public final class KeYModelUtil {
   /**
    * Forbid instances.
    */
   private KeYModelUtil() {
   }

   /**
    * <p>
    * Creates new {@link IKeYSEDDebugNode}s for new {@link IExecutionNode}s
    * which are added after the existing {@link IKeYSEDDebugNode}s.
    * </p>
    * <p>
    * The assumption is that new children are only added in the end and
    * that existing children are never replaced or removed.
    * </p>
    * @param parent The parent {@link IKeYSEDDebugNode} in the debug model.
    * @param oldChildren The existing {@link IKeYSEDDebugNode}s to keep.
    * @param executionChildren The {@link IExecutionNode}s of the execution tree to create debug model representations for.
    * @return The created debug model representations.
    * @throws DebugException Occurred Exception.
    */
   public static IKeYSEDDebugNode<?>[] updateChildren(IKeYSEDDebugNode<?> parent, 
                                                      IKeYSEDDebugNode<?>[] oldChildren, 
                                                      IExecutionNode[] executionChildren) throws DebugException {
      if (executionChildren != null) {
         IKeYSEDDebugNode<?>[] result = new IKeYSEDDebugNode<?>[executionChildren.length];
         // Add old children
         System.arraycopy(oldChildren, 0, result, 0, oldChildren.length);
         // Create new children
         for (int i = oldChildren.length; i < executionChildren.length; i++) {
            result[i] = createChild(parent, executionChildren[i]);
         }
         return result;
      }
      else {
         return new IKeYSEDDebugNode<?>[0];
      }
   }
   
   /**
    * Creates new {@link IKeYSEDDebugNode}s for the given {@link IExecutionNode}s.
    * @param parent The parent {@link IKeYSEDDebugNode} in the debug model.
    * @param executionChildren The {@link IExecutionNode}s of the execution tree to create debug model representations for.
    * @return The created debug model representations.
    * @throws DebugException Occurred Exception.
    */
   public static IKeYSEDDebugNode<?>[] createChildren(IKeYSEDDebugNode<?> parent, 
                                                      IExecutionNode[] executionChildren) throws DebugException {
      if (executionChildren != null) {
         IKeYSEDDebugNode<?>[] result = new IKeYSEDDebugNode<?>[executionChildren.length];
         for (int i = 0; i < executionChildren.length; i++) {
            result[i] = createChild(parent, executionChildren[i]);
         }
         return result;
      }
      else {
         return new IKeYSEDDebugNode<?>[0];
      }
   }

   /**
    * Creates an {@link IKeYSEDDebugNode} for the given {@link IExecutionNode}
    * as child of the given parent {@link IKeYSEDDebugNode}.
    * @param parent The parent {@link IKeYSEDDebugNode} in the debug model.
    * @param executionNode The {@link IExecutionNode} of the execution tree.
    * @return The created {@link IKeYSEDDebugNode}.
    * @throws DebugException Occurred Exception.
    */
   protected static IKeYSEDDebugNode<?> createChild(IKeYSEDDebugNode<?> parent, IExecutionNode executionNode) throws DebugException {
      KeYDebugTarget target = parent.getDebugTarget();
      KeYThread thread = parent.getThread();
      IKeYSEDDebugNode<?> result;
      if (executionNode instanceof IExecutionBranchCondition) {
         result = new KeYBranchCondition(target, parent, thread, (IExecutionBranchCondition)executionNode);
      }
      else if (executionNode instanceof IExecutionBranchStatement) {
         result = new KeYBranchStatement(target, parent, thread, (IExecutionBranchStatement)executionNode);
      }
      else if (executionNode instanceof IExecutionLoopCondition) {
         result = new KeYLoopCondition(target, parent, thread, (IExecutionLoopCondition)executionNode);
      }
      else if (executionNode instanceof IExecutionLoopStatement) {
         result = new KeYLoopStatement(target, parent, thread, (IExecutionLoopStatement)executionNode);
      }
      else if (executionNode instanceof IExecutionMethodCall) {
         result = new KeYMethodCall(target, parent, thread, (IExecutionMethodCall)executionNode);
      }
      else if (executionNode instanceof IExecutionMethodReturn) {
         IExecutionMethodReturn executionReturn = ((IExecutionMethodReturn)executionNode);
         IKeYSEDDebugNode<?> callNode = target.getDebugNode(executionReturn.getMethodCall());
         Assert.isTrue(callNode instanceof KeYMethodCall);
         KeYMethodCall keyCall = (KeYMethodCall)callNode;
         result = createMethodReturn(target, thread, parent, keyCall, executionReturn);
      }
      else if (executionNode instanceof IExecutionStatement) {
         result = new KeYStatement(target, parent, thread, (IExecutionStatement)executionNode);
      }
      else if (executionNode instanceof IExecutionOperationContract) {
         result = new KeYMethodContract(target, parent, thread, (IExecutionOperationContract)executionNode);
      }
      else if (executionNode instanceof IExecutionLoopInvariant) {
         result = new KeYLoopInvariant(target, parent, thread, (IExecutionLoopInvariant)executionNode);
      }
      else if (executionNode instanceof IExecutionTermination) {
         IExecutionTermination terminationExecutionNode = (IExecutionTermination)executionNode;
         result = createTermination(target, thread, parent, terminationExecutionNode);
      }
      else {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Not supported execution node \"" + executionNode + "\"."));
      }
      return result;
   }
   
   /**
    * Creates the {@link KeYMethodReturn} for the given {@link IExecutionMethodReturn}.
    * @param target The {@link KeYDebugTarget} to use.
    * @param thread The parent {@link KeYThread}.
    * @param parent The parent {@link IKeYSEDDebugNode} in the debug model.
    * @param keyCall The {@link KeYMethodCall} which is returned by the given {@link IExecutionMethodReturn}.
    * @param executionReturn The {@link IExecutionMethodReturn} of the execution tree.
    * @return The {@link KeYMethodReturn} for the given {@link IExecutionTermination}.
    * @throws DebugException Occurred Exception.
    */
   public static KeYMethodReturn createMethodReturn(KeYDebugTarget target, 
                                                    KeYThread thread, 
                                                    IKeYSEDDebugNode<?> parent, 
                                                    KeYMethodCall keyCall, 
                                                    IExecutionMethodReturn executionReturn) throws DebugException {
      synchronized (keyCall) {
         KeYMethodReturn resultReturn = keyCall.getMethodReturn(executionReturn);
         if (resultReturn != null) {
            // Reuse method return created by the method call and set its parent now
            if (resultReturn.getParent() == null) {
               resultReturn.setParent(parent);
            }
            else {
               Assert.isTrue(resultReturn.getParent() == parent);
            }
            return resultReturn;
         }
         else {
            // Create new method return
            return new KeYMethodReturn(target, parent, thread, keyCall, executionReturn);
         }
      }
   }
   
   /**
    * Creates the termination node for the given {@link IExecutionTermination}.
    * @param target The {@link KeYDebugTarget} to use.
    * @param thread The parent {@link KeYThread}.
    * @param parent The parent {@link IKeYSEDDebugNode} in the debug model.
    * @param terminationExecutionNode The {@link IExecutionTermination} of the execution tree.
    * @return The termination node for the given {@link IExecutionTermination}.
    * @throws DebugException Occurred Exception.
    */
   public static IKeYSEDDebugNode<?> createTermination(KeYDebugTarget target, 
                                                       KeYThread thread, 
                                                       IKeYSEDDebugNode<?> parent, 
                                                       IExecutionTermination terminationExecutionNode) throws DebugException {
      synchronized (thread) {
         ISEDTermination terminationNode = thread.getTermination(terminationExecutionNode);
         if (terminationNode != null) {
            // Reuse method return created by the method call and set its parent now
            if (terminationNode.getParent() == null) {
               if (terminationNode instanceof KeYExceptionalTermination) {
                  ((KeYExceptionalTermination)terminationNode).setParent(parent);
               }
               else if (terminationNode instanceof KeYTermination) {
                  ((KeYTermination)terminationNode).setParent(parent);
               }
               else if (terminationNode instanceof KeYLoopBodyTermination) {
                  ((KeYLoopBodyTermination)terminationNode).setParent(parent);
               }
               else {
                  throw new DebugException(LogUtil.getLogger().createErrorStatus("Not supported termination \"" + terminationNode + "\"."));
               }
            }
            else {
               Assert.isTrue(terminationNode.getParent() == parent);
            }
            return (IKeYSEDDebugNode<?>)terminationNode;
         }
         else {
            // Create new termination
            if (terminationExecutionNode.getTerminationKind() == TerminationKind.EXCEPTIONAL) {
               return new KeYExceptionalTermination(target, parent, thread, terminationExecutionNode);
            }
            else if (terminationExecutionNode.getTerminationKind() == TerminationKind.NORMAL) {
               return new KeYTermination(target, parent, thread, terminationExecutionNode);
            }
            else if (terminationExecutionNode.getTerminationKind() == TerminationKind.LOOP_BODY) {
               return new KeYLoopBodyTermination(target, parent, thread, terminationExecutionNode);
            }
            else {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Not supported termination kind \"" + terminationExecutionNode.getTerminationKind() + "\"."));
            }
         }
      }
   }
   
   /**
    * Tries to update the given {@link SourceLocation} of the given
    * {@link IStackFrame} with the location provided by JDT. If possible
    * the new location is returned and the original location otherwise.
    * @param frame The {@link IStackFrame} which defines the file to parse.
    * @param sourceLocation The {@link SourceLocation} which describes the {@link ASTNode} to update location from.
    * @return The updated {@link SourceLocation} or the initial {@link SourceLocation}.
    * @throws DebugException Occurred Exception.
    */
   public static SourceLocation updateLocationFromAST(IStackFrame frame,
                                                      SourceLocation sourceLocation) throws DebugException {
      try {
         ASTNode statementNode = findASTNode(frame, sourceLocation);
         return updateLocationFromAST(sourceLocation, statementNode);
      }
      catch (Exception e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
   }
   
   /**
    * Tries to update the given {@link SourceLocation} of the given
    * {@link IStackFrame} with the location provided by JDT. If possible
    * the new location is returned and the original location otherwise.    * @param locationToUpdate The {@link SourceLocation} to return if no {@link ASTNode} is defined.
    * @param nodeToExtractLocationFrom An optional {@link ASTNode} which source location should replace the given one.
    * @return The updated {@link SourceLocation} or the initial {@link SourceLocation}.
    */
   public static SourceLocation updateLocationFromAST(SourceLocation locationToUpdate,
                                                      ASTNode nodeToExtractLocationFrom) {
      SourceLocation result = locationToUpdate;
      if (nodeToExtractLocationFrom != null) {
         result = new SourceLocation(-1, 
                                     nodeToExtractLocationFrom.getStartPosition(), 
                                     nodeToExtractLocationFrom.getStartPosition() + nodeToExtractLocationFrom.getLength());
      }
      return result;
   }
   
   /**
    * Searches the {@link ASTNode} in JDT which described by the given 
    * {@link IStackFrame} and the {@link SourceLocation}.
    * @param frame The {@link IStackFrame} which defines the file to parse.
    * @param sourceLocation The {@link SourceLocation} which describes the {@link ASTNode} to return.
    * @return The found {@link ASTNode} or {@code null} if not available.
    */
   public static ASTNode findASTNode(IStackFrame frame,
                                     SourceLocation sourceLocation) {
      ASTNode statementNode = null;
      if (sourceLocation != null && sourceLocation.getCharEnd() >= 0) {
         ICompilationUnit compilationUnit = findCompilationUnit(frame);
         if (compilationUnit != null) {
            ASTNode root = JDTUtil.parse(compilationUnit, sourceLocation.getCharStart(), sourceLocation.getCharEnd() - sourceLocation.getCharStart());
            statementNode = ASTNodeByEndIndexSearcher.search(root, sourceLocation.getCharEnd());
         }
      }
      return statementNode;
   }

   /**
    * Tries to find an {@link ICompilationUnit} for the given {@link IStackFrame}.
    * @param frame The given {@link IStackFrame} for that is an {@link ICompilationUnit} required.
    * @return The found {@link ICompilationUnit}.
    */
   public static ICompilationUnit findCompilationUnit(IStackFrame frame) {
      ICompilationUnit result = null;
      if (frame != null) {
         Object source = frame.getLaunch().getSourceLocator().getSourceElement(frame);
         if (source instanceof IFile) {
            IJavaElement element = JavaCore.create((IFile)source);
            if (element instanceof ICompilationUnit) {
               result = (ICompilationUnit)element;
            }
         }
      }
      return result;
   }

   /**
    * Creates debug model representations for the {@link IExecutionVariable}s
    * contained in the given {@link IExecutionStateNode}.
    * @param debugNode The {@link IKeYSEDDebugNode} which should be used as parent.
    * @param executionNode The {@link IExecutionStateNode} to return its variables.
    * @return The contained {@link KeYVariable}s as debug model representation.
    */
   public static KeYVariable[] createVariables(IKeYSEDDebugNode<?> debugNode, 
                                               IExecutionStateNode<?> executionNode) {
      if (executionNode != null && !executionNode.isDisposed() && debugNode != null) {
         IExecutionVariable[] variables = executionNode.getVariables();
         if (variables != null) {
            KeYVariable[] result = new KeYVariable[variables.length];
            for (int i = 0; i < variables.length; i++) {
               result[i] = new KeYVariable(debugNode.getDebugTarget(), variables[i]);
            }
            return result;
         }
         else {
            return new KeYVariable[0];
         }
      }
      else {
         return new KeYVariable[0];
      }
   }

   /**
    * Converts the given call stack of {@link IExecutionNode} into 
    * a call stack of {@link ISEDDebugNode}s.
    * @param debugTarget The {@link KeYDebugTarget} which maps {@link IExecutionNode}s to {@link ISEDDebugNode}s.
    * @param callStack The call stack to convert.
    * @return The converted call stack.
    */
   public static IKeYSEDDebugNode<?>[] createCallStack(KeYDebugTarget debugTarget, IExecutionNode[] callStack) {
      if (debugTarget != null && callStack != null) {
         IKeYSEDDebugNode<?>[] result = new IKeYSEDDebugNode<?>[callStack.length];
         int i = 0;
         for (IExecutionNode executionNode : callStack) {
            IKeYSEDDebugNode<?> debugNode = debugTarget.getDebugNode(executionNode);
            Assert.isNotNull(debugNode, "Can't find debug node for execution node \"" + executionNode + "\".");
            result[i] = debugNode;
            i++;
         }
         return result;
      }
      else {
         return new IKeYSEDDebugNode<?>[0];
      }
   }
}