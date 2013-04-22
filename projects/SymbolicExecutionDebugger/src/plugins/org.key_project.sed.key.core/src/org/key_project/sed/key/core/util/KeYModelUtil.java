/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

import java.io.File;
import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.ASTNode;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.sed.key.core.model.KeYBranchCondition;
import org.key_project.sed.key.core.model.KeYBranchNode;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.model.KeYExceptionalTermination;
import org.key_project.sed.key.core.model.KeYLoopBodyTermination;
import org.key_project.sed.key.core.model.KeYLoopCondition;
import org.key_project.sed.key.core.model.KeYLoopNode;
import org.key_project.sed.key.core.model.KeYMethodCall;
import org.key_project.sed.key.core.model.KeYMethodReturn;
import org.key_project.sed.key.core.model.KeYStatement;
import org.key_project.sed.key.core.model.KeYTermination;
import org.key_project.sed.key.core.model.KeYUseLoopInvariant;
import org.key_project.sed.key.core.model.KeYUseOperationContract;
import org.key_project.sed.key.core.model.KeYVariable;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IOUtil.LineInformation;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination.TerminationKind;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionUseLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionUseOperationContract;
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
      ISEDThread thread = parent.getThread();
      IKeYSEDDebugNode<?> result;
      if (executionNode instanceof IExecutionBranchCondition) {
         result = new KeYBranchCondition(target, parent, thread, (IExecutionBranchCondition)executionNode);
      }
      else if (executionNode instanceof IExecutionBranchNode) {
         result = new KeYBranchNode(target, parent, thread, (IExecutionBranchNode)executionNode);
      }
      else if (executionNode instanceof IExecutionLoopCondition) {
         result = new KeYLoopCondition(target, parent, thread, (IExecutionLoopCondition)executionNode);
      }
      else if (executionNode instanceof IExecutionLoopNode) {
         result = new KeYLoopNode(target, parent, thread, (IExecutionLoopNode)executionNode);
      }
      else if (executionNode instanceof IExecutionMethodCall) {
         result = new KeYMethodCall(target, parent, thread, (IExecutionMethodCall)executionNode);
      }
      else if (executionNode instanceof IExecutionMethodReturn) {
         result = new KeYMethodReturn(target, parent, thread, (IExecutionMethodReturn)executionNode);
      }
      else if (executionNode instanceof IExecutionStatement) {
         result = new KeYStatement(target, parent, thread, (IExecutionStatement)executionNode);
      }
      else if (executionNode instanceof IExecutionUseOperationContract) {
         result = new KeYUseOperationContract(target, parent, thread, (IExecutionUseOperationContract)executionNode);
      }
      else if (executionNode instanceof IExecutionUseLoopInvariant) {
         result = new KeYUseLoopInvariant(target, parent, thread, (IExecutionUseLoopInvariant)executionNode);
      }
      else if (executionNode instanceof IExecutionTermination) {
         IExecutionTermination terminationExecutionNode = (IExecutionTermination)executionNode;
         if (terminationExecutionNode.getTerminationKind() == TerminationKind.EXCEPTIONAL) {
            result = new KeYExceptionalTermination(target, parent, thread, (IExecutionTermination)executionNode);
         }
         else if (terminationExecutionNode.getTerminationKind() == TerminationKind.NORMAL) {
            result = new KeYTermination(target, parent, thread, (IExecutionTermination)executionNode);
         }
         else if (terminationExecutionNode.getTerminationKind() == TerminationKind.LOOP_BODY) {
            result = new KeYLoopBodyTermination(target, parent, thread, (IExecutionTermination)executionNode);
         }
         else {
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Not supported termination kind \"" + terminationExecutionNode.getTerminationKind() + "\"."));
         }
      }
      else {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Not supported execution node \"" + executionNode + "\"."));
      }
      target.registerDebugNode(result);
      return result;
   }
   
   /**
    * Returns the path to the source file defined by the given {@link PositionInfo}.
    * @param posInfo The {@link PositionInfo} to extract source file from.
    * @return The source file name or {@code null} if not available.
    */
   public static String getSourcePath(PositionInfo posInfo) {
      String result = null;
      if (posInfo.getFileName() != null) {
         result = posInfo.getFileName(); // posInfo.getFileName() is a path to a file
      }
      else if (posInfo.getParentClass() != null) {
         result = posInfo.getParentClass(); // posInfo.getParentClass() is a path to a file
      }
      if (result != null && result.startsWith("FILE:")) {
         result = result.substring("FILE:".length());
      }
      return result;
   }

   /**
    * Converts the given {@link PositionInfo} into a {@link SourceLocation}.
    * This includes to convert position information defined via row and column
    * of the {@link PositionInfo} into character offset from file beginning
    * for the {@link SourceLocation}.
    * @param posInfo The {@link PositionInfo} to convert.
    * @return The created {@link PositionInfo}.
    */
   public static SourceLocation convertToSourceLocation(PositionInfo posInfo) {
      try {
         if (posInfo != null && posInfo != PositionInfo.UNDEFINED) {
            // Try to find the source file.
            String path = getSourcePath(posInfo);
            File file = path != null ? new File(path) : null;
            // Check if a source file is available
            int charStart = -1;
            int charEnd = -1;
            int lineNumber = -1;
            if (file != null) {
               // Set source location
               LineInformation[] infos = IOUtil.computeLineInformation(file);
               if (posInfo.getStartPosition() != null) {
                  int line = posInfo.getStartPosition().getLine() - 1;
                  int column = posInfo.getStartPosition().getColumn();
                  if (line >= 0 && line < infos.length) {
                     LineInformation info = infos[line];
                     int offset = info.getOffset() + KeYUtil.normalizeRecorderColumn(column, info.getTabIndices());
                     charStart = offset;
                  }
               }
               if (posInfo.getEndPosition() != null) {
                  int line = posInfo.getEndPosition().getLine() - 1;
                  int column = posInfo.getEndPosition().getColumn();
                  if (line >= 0 && line < infos.length) {
                     LineInformation info = infos[line];
                     int offset = info.getOffset() + KeYUtil.normalizeRecorderColumn(column, info.getTabIndices());
                     charEnd = offset;
                  }
               }
               // Check if source start and end is defined.
               if (charStart < 0 || charEnd < 0) {
                  // Unset start and end indices
                  charStart = -1;
                  charEnd = -1;
                  // Try to set a line number as backup
                  if (posInfo.getEndPosition() != null) {
                     lineNumber = posInfo.getEndPosition().getLine();
                  }
               }
               return new SourceLocation(lineNumber, charStart, charEnd);
            }
            else {
               return SourceLocation.UNDEFINED;
            }
         }
         else {
            return SourceLocation.UNDEFINED;
         }
      }
      catch (IOException e) {
         LogUtil.getLogger().logError(e);
         return SourceLocation.UNDEFINED;
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
    * Searches the {@link IMethod} as JDT representation which ends
    * at the given index.
    * @param cu The {@link ICompilationUnit} to search in.
    * @param endIndex The index in the file at that the required method ends.
    * @return The found {@link IMethod} or {@code null} if the JDT representation is not available.
    * @throws JavaModelException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public static IMethod findJDTMethod(ICompilationUnit cu, int endIndex) throws JavaModelException, IOException {
      IMethod result = null;
      if (cu != null) {
         IType[] types = cu.getAllTypes();
         int i = 0;
         while (result == null && i < types.length) {
            IMethod[] methods = types[i].getMethods();
            int j = 0;
            while (result == null && j < methods.length) {
               ISourceRange methodRange = methods[j].getSourceRange();
               if (endIndex == methodRange.getOffset() + methodRange.getLength()) {
                  result = methods[j];
               }
               j++;
            }
            i++;
         }
      }
      return result;
   }
   
   /**
    * Represents a location in a source file.
    * @author Martin Hentschel
    */
   public static class SourceLocation {
      /**
       * Location which indicates that no location is defined.
       */
      public static final SourceLocation UNDEFINED = new SourceLocation(-1, -1, -1);
      
      /**
       * The line number to select.
       */
      private int lineNumber;
      
      /**
       * The index of the start character to select.
       */
      private int charStart;
      
      /**
       * The index of the end character to select.
       */
      private int charEnd;
      
      /**
       * Constructor.
       * @param lineNumber The line number to select.
       * @param charStart The index of the start character to select.
       * @param charEnd The index of the end character to select.
       */
      public SourceLocation(int lineNumber, int charStart, int charEnd) {
         super();
         this.lineNumber = lineNumber;
         this.charStart = charStart;
         this.charEnd = charEnd;
      }
      
      /**
       * Returns The line number to select.
       * @return The line number to select.
       */
      public int getLineNumber() {
         return lineNumber;
      }
      
      /**
       * Returns The index of the start character to select.
       * @return The index of the start character to select.
       */
      public int getCharStart() {
         return charStart;
      }
      
      /**
       * Returns The index of the end character to select.
       * @return The index of the end character to select.
       */
      public int getCharEnd() {
         return charEnd;
      }
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
