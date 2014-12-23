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

package org.key_project.sed.key.core.breakpoints;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaClassPrepareBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaExceptionBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaLineBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaMethodBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaWatchpoint;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.FieldWatchpoint;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.LineBreakpoint;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.MethodBreakpoint;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.SymbolicExecutionExceptionBreakpoint;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

// TODO: Document class
@SuppressWarnings("restriction")
public class KeYBreakpointManager {
   /**
    * The {@link SymbolicExecutionBreakpointStopCondition} that holds all {@link de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint} for this {@link KeYDebugTarget}.
    */
   private final SymbolicExecutionBreakpointStopCondition breakpointStopCondition = new SymbolicExecutionBreakpointStopCondition();

   /**
    * The Map of {@link JavaLineBreakpoint}s with their current HitCount as value.
    */
   private final Map<IBreakpoint, de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint> breakpointMap;
   
   /**
    * Creates a new {@link KeYBreakpointManager}
    */
   public KeYBreakpointManager(){
      breakpointMap = new HashMap<IBreakpoint, de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint>();
   }
   
   /**
    * Handles the event of a {@link KeYWatchpoint} being added
    * 
    * @param watchpoint the {@link KeYWatchpoint} to be added
    * @param environment the {@link SymbolicExecutionEnvironment<?>} belonging to the respective {@link KeYDebugTarget}
    * @throws CoreException
    * @throws ProofInputException
    */
   public void keyWatchpointAdded(KeYWatchpoint watchpoint, SymbolicExecutionEnvironment<?> environment) throws CoreException, ProofInputException {
      IResource resource = watchpoint.getMarker().getResource();
      if (JDTUtil.isJavaFile(resource)) {
         JavaInfo javaInfo = environment.getServices().getJavaInfo();
         String containerTypeName = KeYUtil.getType(resource).getFullyQualifiedName();
         containerTypeName = containerTypeName.replace('$', '.'); // Inner and anonymous classes are separated with '.' instead of '$' in KeY
         KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
         if (containerKJT != null) {
            de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.KeYWatchpoint stopCondition = new de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.KeYWatchpoint(
                  watchpoint.getHitCount(), environment
                  .getBuilder().getProof(),
                  watchpoint.getCondition(), watchpoint.isEnabled(),
                  watchpoint.isConditionEnabled(), containerKJT, watchpoint.isSuspendOnTrue());
            breakpointStopCondition.addBreakpoint(stopCondition);
            breakpointMap.put(watchpoint, stopCondition);
         }
      }
   }

   /**
    * Handles the event of a {@link JavaMethodBreakpoint} being added
    * 
    * @param methodBreakpoint the {@link JavaMethodBreakpoint} to be added
    * @param environment the {@link SymbolicExecutionEnvironment<?>} belonging to the respective {@link KeYDebugTarget}
    * @throws CoreException
    * @throws ProofInputException
    */
   public void methodBreakpointAdded(JavaMethodBreakpoint methodBreakpoint, SymbolicExecutionEnvironment<?> environment) throws CoreException, ProofInputException {
      IResource resource = methodBreakpoint.getMarker().getResource();
      if (JDTUtil.isJavaFile(resource)) {
         IMethod method = KeYUtil.getContainingMethodForMethodStart(methodBreakpoint.getCharStart(), resource);
         if (method != null) {
            // Determine container type
            IType containerType = method.getDeclaringType();
            String containerTypeName = containerType.getFullyQualifiedName();
            containerTypeName = containerTypeName.replace('$', '.'); // Inner and anonymous classes are separated with '.' instead of '$' in KeY
            KeYJavaType containerKJT = environment.getBuilder().getProof().getJavaInfo().getTypeByClassName(containerTypeName);
            if(containerKJT!=null){
               IProgramMethod pm = KeYUtil.getProgramMethod(method, environment.getProof().getJavaInfo());
               int start = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset());
               int end = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset() + method.getSourceRange().getLength());
               MethodBreakpoint stopCondition = new MethodBreakpoint(
                     methodBreakpoint.getMarker().getResource().getLocation().toOSString(),
                     methodBreakpoint.getLineNumber(),
                     methodBreakpoint.getHitCount(), pm, environment
                           .getBuilder().getProof(),
                           methodBreakpoint.getCondition(), methodBreakpoint.isEnabled(),
                           methodBreakpoint.isConditionEnabled(), start, end, methodBreakpoint.isEntry(), methodBreakpoint.isExit());
               breakpointStopCondition.addBreakpoint(stopCondition);
               breakpointMap.put(methodBreakpoint, stopCondition);
            }
         }
      }
   }

   /**
    * Handles the event of a {@link JavaWatchpoint} being added
    * 
    * @param javaWatchpoint the {@link JavaWatchpoint} to be added
    * @param environment the {@link SymbolicExecutionEnvironment<?>} belonging to the respective {@link KeYDebugTarget}
    * @throws CoreException
    * @throws ProofInputException
    */
   public void javaWatchpointAdded(JavaWatchpoint javaWatchpoint, SymbolicExecutionEnvironment<?> environment) throws CoreException, ProofInputException {
      IResource resource = javaWatchpoint.getMarker().getResource();
      if (JDTUtil.isJavaFile(resource)) {
         JavaInfo javaInfo = environment.getServices().getJavaInfo();
         String containerTypeName = KeYUtil.getType(resource).getFullyQualifiedName();
         containerTypeName = containerTypeName.replace('$', '.'); // Inner and anonymous classes are separated with '.' instead of '$' in KeY
         KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
         if(containerKJT!=null){
            FieldWatchpoint stopCondition = new FieldWatchpoint(javaWatchpoint.isEnabled(),javaWatchpoint.getHitCount(),
                  javaWatchpoint.getFieldName(), javaWatchpoint.isAccess(), javaWatchpoint.isModification(), containerKJT,
                  environment.getBuilder().getProof());
            breakpointStopCondition.addBreakpoint(stopCondition);
            breakpointMap.put(javaWatchpoint, stopCondition);
         }
      }
   }

   /**
    * Handles the event of a {@link JavaExceptionBreakpoint} being added
    * 
    * @param exceptionBreakpoint the {@link JavaExceptionBreakpoint} to be added
    * @param environment the {@link SymbolicExecutionEnvironment<?>} belonging to the respective {@link KeYDebugTarget}
    * @throws CoreException
    * @throws ProofInputException
    */
   public void exceptionBreakpointAdded(JavaExceptionBreakpoint exceptionBreakpoint, SymbolicExecutionEnvironment<?> environment) throws CoreException {
      SymbolicExecutionExceptionBreakpoint stopCondition = new SymbolicExecutionExceptionBreakpoint(environment.getBuilder().getProof(),exceptionBreakpoint.getTypeName(),
            exceptionBreakpoint.isCaught(), exceptionBreakpoint.isUncaught(), exceptionBreakpoint.isSuspendOnSubclasses(),
            exceptionBreakpoint.isEnabled(), exceptionBreakpoint.getHitCount());
      breakpointStopCondition.addBreakpoint(stopCondition);
      breakpointMap.put(exceptionBreakpoint, stopCondition);
      
   }

   /**
    * Handles the event of a {@link JavaLineBreakpoint} being added
    * 
    * @param lineBreakpoint the {@link JavaLineBreakpoint} to be added
    * @param environment the {@link SymbolicExecutionEnvironment<?>} belonging to the respective {@link KeYDebugTarget}
    * @throws CoreException
    * @throws ProofInputException
    */
   public void lineBreakpointAdded(JavaLineBreakpoint lineBreakpoint, SymbolicExecutionEnvironment<?> environment) throws CoreException, ProofInputException {
      IResource resource = lineBreakpoint.getMarker().getResource();
      if (JDTUtil.isJavaFile(resource)) {
         IMethod method = KeYUtil.getContainingMethod(lineBreakpoint.getLineNumber(), resource);
         if (method != null) {
            // Determine container type
            IType containerType = method.getDeclaringType();
            String containerTypeName = containerType.getFullyQualifiedName();
            containerTypeName = containerTypeName.replace('$', '.'); // Inner and anonymous classes are separated with '.' instead of '$' in KeY
            KeYJavaType containerKJT = environment.getBuilder().getProof().getJavaInfo().getTypeByClassName(containerTypeName);
            if(containerKJT!=null){
               IProgramMethod pm = KeYUtil.getProgramMethod(method, environment.getProof().getJavaInfo());
               int start = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset());
               int end = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset() + method.getSourceRange().getLength());
               LineBreakpoint stopCondition = new LineBreakpoint(
                     resource.getLocation().toOSString(),
                     lineBreakpoint.getLineNumber(),
                     lineBreakpoint.getHitCount(), pm, environment
                           .getBuilder().getProof(),
                     lineBreakpoint.getCondition(), lineBreakpoint.isEnabled(),
                     lineBreakpoint.isConditionEnabled(), start, end);
               breakpointStopCondition.addBreakpoint(stopCondition);
               breakpointMap.put(lineBreakpoint, stopCondition);
            }
         }
      }
   }

   /**
    * Handles the event of a breakpoint being removed from a {@link KeYDebugTarget}.
    * 
    * @param breakpoint that is being removed
    * @param delta the associated marker delta, or null when the breakpoint is removed from the breakpoint manager without being deleted
    */
   public void breakpointRemoved(IBreakpoint breakpoint, IMarkerDelta delta) {
      if(breakpoint instanceof JavaMethodBreakpoint){
         JavaMethodBreakpoint methodBreakpoint = (JavaMethodBreakpoint) breakpoint;
         breakpointStopCondition.removeBreakpoint(breakpointMap.get(methodBreakpoint));
         breakpointMap.remove(methodBreakpoint);
      } else if(breakpoint instanceof JavaWatchpoint){
         JavaWatchpoint javaWatchpoint = (JavaWatchpoint) breakpoint;
         breakpointStopCondition.removeBreakpoint(breakpointMap.get(javaWatchpoint));
         breakpointMap.remove(javaWatchpoint);
      } else if(breakpoint instanceof JavaClassPrepareBreakpoint){
         JavaClassPrepareBreakpoint javaClassPrepareBreakpoint = (JavaClassPrepareBreakpoint) breakpoint;
         breakpointStopCondition.removeBreakpoint(breakpointMap.get(javaClassPrepareBreakpoint));
         breakpointMap.remove(javaClassPrepareBreakpoint);
      } else if(breakpoint instanceof JavaLineBreakpoint){
         JavaLineBreakpoint lineBreakpoint = (JavaLineBreakpoint) breakpoint;
         breakpointStopCondition.removeBreakpoint(breakpointMap.get(lineBreakpoint));
         breakpointMap.remove(lineBreakpoint);
      } else if(breakpoint instanceof JavaExceptionBreakpoint){
         JavaExceptionBreakpoint exceptionBreakpoint = (JavaExceptionBreakpoint) breakpoint;
         breakpointStopCondition.removeBreakpoint(breakpointMap.get(exceptionBreakpoint));
         breakpointMap.remove(exceptionBreakpoint);
      } else if(breakpoint instanceof KeYWatchpoint){
         KeYWatchpoint watchpoint = (KeYWatchpoint) breakpoint;
         breakpointStopCondition.removeBreakpoint(breakpointMap.get(watchpoint));
         breakpointMap.remove(watchpoint);
      }
   }  

   /**
    * Handles the event of an existing {@link KeYWatchpoint} being changed
    * 
    * @param watchpoint the {@link KeYWatchpoint} to be changed
    * @throws CoreException
    * @throws ProofInputException
    */
   public void keyWatchpointChanged(KeYWatchpoint watchpoint) throws SLTranslationException, CoreException {
      KeYWatchpoint stopCondition = (KeYWatchpoint) breakpointMap.get(watchpoint);
      if (stopCondition != null) {
         stopCondition.setEnabled(watchpoint.isEnabled());
         stopCondition.setHitCount(watchpoint.getHitCount());
         stopCondition.setConditionEnabled(watchpoint.isConditionEnabled());
         stopCondition.setCondition(watchpoint.getCondition());
         stopCondition.setSuspendOnTrue(watchpoint.isSuspendOnTrue());
      }
   }

   /**
    * Handles the event of an existing {@link JavaExceptionBreakpoint} being changed
    * 
    * @param exceptionBreakpoint the {@link JavaExceptionBreakpoint} to be changed
    * @throws CoreException
    * @throws ProofInputException
    */
   public void exceptionBreakpointChanged(JavaExceptionBreakpoint exceptionBreakpoint) throws CoreException {
      SymbolicExecutionExceptionBreakpoint stopCondition = (SymbolicExecutionExceptionBreakpoint) breakpointMap.get(exceptionBreakpoint);
      if (stopCondition != null) {
         stopCondition.setEnabled(exceptionBreakpoint.isEnabled());
         stopCondition.setCaught(exceptionBreakpoint.isCaught());
         stopCondition.setUncaught(exceptionBreakpoint.isUncaught());
         stopCondition.setSuspendOnSubclasses(exceptionBreakpoint.isSuspendOnSubclasses());
         stopCondition.setHitCount(exceptionBreakpoint.getHitCount());
      }
   }

   /**
    * Handles the event of an existing {@link JavaLineBreakpoint} being changed
    * 
    * @param lineBreakpoint the {@link JavaLineBreakpoint} to be changed
    * @throws CoreException
    * @throws ProofInputException
    */
   public void javaLineBreakpointAdded(JavaLineBreakpoint lineBreakpoint) throws CoreException, SLTranslationException {
      LineBreakpoint stopCondition = (LineBreakpoint) breakpointMap.get(lineBreakpoint);
      if (stopCondition != null) {
         stopCondition.setHitCount(lineBreakpoint.getHitCount());
         stopCondition.setEnabled(lineBreakpoint.isEnabled());
         stopCondition.setConditionEnabled(lineBreakpoint.isConditionEnabled());
         stopCondition.setCondition(lineBreakpoint.getCondition());
      }
   }

   /**
    * Handles the event of an existing {@link JavaWatchpoint} being changed
    * 
    * @param javaWatchpoint the {@link JavaWatchpoint} to be changed
    * @throws CoreException
    * @throws ProofInputException
    */
   public void javaWatchpointChanged(JavaWatchpoint javaWatchpoint) throws CoreException {
      FieldWatchpoint stopCondition = (FieldWatchpoint) breakpointMap.get(javaWatchpoint);
      if (stopCondition != null) {
         stopCondition.setHitCount(javaWatchpoint.getHitCount());
         stopCondition.setEnabled(javaWatchpoint.isEnabled());
         stopCondition.setAccess(javaWatchpoint.isAccess());
         stopCondition.setModification(javaWatchpoint.isModification());
      }
   }

   /**
    * Handles the event of an existing {@link JavaMethodBreakpoint} being changed
    * 
    * @param methodBreakpoint the {@link JavaMethodBreakpoint} to be changed
    * @throws CoreException
    * @throws ProofInputException
    */
   public void methodBreakpointChanged(JavaMethodBreakpoint methodBreakpoint) throws CoreException, SLTranslationException {
      MethodBreakpoint stopCondition = (MethodBreakpoint) breakpointMap.get(methodBreakpoint);
      if (stopCondition != null) {
         stopCondition.setHitCount(methodBreakpoint.getHitCount());
         stopCondition.setEnabled(methodBreakpoint.isEnabled());
         stopCondition.setConditionEnabled(methodBreakpoint.isConditionEnabled());
         stopCondition.setCondition(methodBreakpoint.getCondition());
         stopCondition.setEntry(methodBreakpoint.isEntry());
         stopCondition.setExit(methodBreakpoint.isExit());
      }
   }

   /**
    * @return the breakpointStopConditions
    */
   public SymbolicExecutionBreakpointStopCondition getBreakpointStopCondition() {
      return breakpointStopCondition;
   }
   
   /**
    * @return the breakpointMap
    */
   public Map<IBreakpoint, de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint> getBreakpointMap() {
      return breakpointMap;
   }

   /**
    * Returns the available {@link IBreakpoint}s.
    * @return The available {@link IBreakpoint}s.
    */
   public IBreakpoint[] getBreakpoints() {
      Set<IBreakpoint> keys = breakpointMap.keySet();
      return keys.toArray(new IBreakpoint[keys.size()]);
   }

   public boolean checkBreakpointHit(IBreakpoint breakpoint, IKeYSEDDebugNode<IExecutionNode<?>> node) {
      de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint keyBreakpoint = breakpointMap.get(breakpoint);
      if (keyBreakpoint != null) {
         IExecutionNode<?> enode = node.getExecutionNode();
         Node proofNode = enode.getProofNode();
         return keyBreakpoint.isBreakpointHit(enode.getActiveStatement(), proofNode.getAppliedRuleApp(), enode.getProof(), proofNode);
      }
      else {
         return false;
      }
   }
}