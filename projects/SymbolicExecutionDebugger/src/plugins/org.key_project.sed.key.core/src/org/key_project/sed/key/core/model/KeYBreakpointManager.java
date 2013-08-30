package org.key_project.sed.key.core.model;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaClassPrepareBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaExceptionBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaLineBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaMethodBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaWatchpoint;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.key.core.breakpoints.KeYWatchpoint;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.ExceptionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.JavaWatchpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.KeYWatchpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.LineBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.MethodBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

@SuppressWarnings("restriction")
public class KeYBreakpointManager {
   
   /**
    * The {@link CompoundStopCondition} that holds all BreakpointsStopCOnditons for this {@link KeYDebugTarget}.
    */
   private CompoundStopCondition breakpointStopConditions = new CompoundStopCondition();

   /**
    * The Map of {@link JavaLineBreakpoint}s with their current HitCount as value.
    */
   private Map<IBreakpoint, IStopCondition> breakpointMap;
   
   /**
    * Creates a new {@link KeYBreakpointManager}
    */
   public KeYBreakpointManager(){
      breakpointMap = new HashMap<IBreakpoint, IStopCondition>();
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
      if (resource.getFileExtension() != null && resource.getFileExtension().equalsIgnoreCase("java")) {
         JavaInfo javaInfo = environment.getServices().getJavaInfo();
         String containerTypeName = KeYUtil.getType(resource).getFullyQualifiedName();
         containerTypeName = containerTypeName.replace('$', '.'); // Inner and anonymous classes are separated with '.' instead of '$' in KeY
         KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
         KeYWatchpointStopCondition stopCondition = new KeYWatchpointStopCondition(
               watchpoint.getHitCount(), environment
               .getBuilder().getProof(), breakpointStopConditions,
               watchpoint.getCondition(), watchpoint.isEnabled(),
               watchpoint.isConditionEnabled(), containerKJT, watchpoint.isSuspendOnTrue());
         breakpointStopConditions.addChildren(stopCondition);
         breakpointMap.put(watchpoint, stopCondition);
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
      if (resource.getFileExtension() != null && resource.getFileExtension().equalsIgnoreCase("java")) {
         IMethod method = KeYUtil.getContainingMethodForMethodStart(methodBreakpoint.getCharStart(), resource);
         IProgramMethod pm = KeYUtil.getProgramMethod(method, environment.getProof().getJavaInfo());
         int start = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset());
         int end = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset() + method.getSourceRange().getLength());
         MethodBreakpointStopCondition stopCondition = new MethodBreakpointStopCondition(
               methodBreakpoint.getMarker().getResource().getLocation().toOSString(),
               methodBreakpoint.getLineNumber(),
               methodBreakpoint.getHitCount(), pm, environment
                     .getBuilder().getProof(), breakpointStopConditions,
                     methodBreakpoint.getCondition(), methodBreakpoint.isEnabled(),
                     methodBreakpoint.isConditionEnabled(), start, end, methodBreakpoint.isEntry(), methodBreakpoint.isExit());
         breakpointStopConditions.addChildren(stopCondition);
         breakpointMap.put(methodBreakpoint, stopCondition);
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
      if (resource.getFileExtension() != null && resource.getFileExtension().equalsIgnoreCase("java")) {
         JavaInfo javaInfo = environment.getServices().getJavaInfo();
         String containerTypeName = KeYUtil.getType(resource).getFullyQualifiedName();
         containerTypeName = containerTypeName.replace('$', '.'); // Inner and anonymous classes are separated with '.' instead of '$' in KeY
         KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
         JavaWatchpointStopCondition stopCondition = new JavaWatchpointStopCondition(javaWatchpoint.isEnabled(),javaWatchpoint.getHitCount(),
                     javaWatchpoint.getFieldName(), javaWatchpoint.isAccess(), breakpointStopConditions, javaWatchpoint.isModification(), containerKJT,
                     environment.getBuilder().getProof());
         breakpointStopConditions.addChildren(stopCondition);
         breakpointMap.put(javaWatchpoint, stopCondition);
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
      ExceptionBreakpointStopCondition stopCondition = new ExceptionBreakpointStopCondition(environment.getBuilder().getProof(),breakpointStopConditions, exceptionBreakpoint.getTypeName(),
            exceptionBreakpoint.isCaught(), exceptionBreakpoint.isUncaught(), exceptionBreakpoint.isSuspendOnSubclasses(),
            exceptionBreakpoint.isEnabled(), exceptionBreakpoint.getHitCount());
      breakpointStopConditions.addChildren(stopCondition);
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
      if (resource.getFileExtension() != null && resource.getFileExtension().equalsIgnoreCase("java")) {
         IMethod method = KeYUtil.getContainingMethod(lineBreakpoint.getLineNumber(), resource);
         IProgramMethod pm = KeYUtil.getProgramMethod(method, environment.getProof().getJavaInfo());
         int start = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset());
         int end = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset() + method.getSourceRange().getLength());
         LineBreakpointStopCondition stopCondition = new LineBreakpointStopCondition(
               resource.getLocation().toOSString(),
               lineBreakpoint.getLineNumber(),
               lineBreakpoint.getHitCount(), pm, environment
                     .getBuilder().getProof(), breakpointStopConditions,
               lineBreakpoint.getCondition(), lineBreakpoint.isEnabled(),
               lineBreakpoint.isConditionEnabled(), start, end);
         breakpointStopConditions.addChildren(stopCondition);
         breakpointMap.put(lineBreakpoint, stopCondition);
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
         breakpointStopConditions.removeChild(breakpointMap.get(methodBreakpoint));
         breakpointMap.remove(methodBreakpoint);
      } else if(breakpoint instanceof JavaWatchpoint){
         JavaWatchpoint javaWatchpoint = (JavaWatchpoint) breakpoint;
         breakpointStopConditions.removeChild(breakpointMap.get(javaWatchpoint));
         breakpointMap.remove(javaWatchpoint);
      } else if(breakpoint instanceof JavaClassPrepareBreakpoint){
         JavaClassPrepareBreakpoint javaClassPrepareBreakpoint = (JavaClassPrepareBreakpoint) breakpoint;
         breakpointStopConditions.removeChild(breakpointMap.get(javaClassPrepareBreakpoint));
         breakpointMap.remove(javaClassPrepareBreakpoint);
      } else if(breakpoint instanceof JavaLineBreakpoint){
         JavaLineBreakpoint lineBreakpoint = (JavaLineBreakpoint) breakpoint;
         breakpointStopConditions.removeChild(breakpointMap.get(lineBreakpoint));
         breakpointMap.remove(lineBreakpoint);
      } else if(breakpoint instanceof JavaExceptionBreakpoint){
         JavaExceptionBreakpoint exceptionBreakpoint = (JavaExceptionBreakpoint) breakpoint;
         breakpointStopConditions.removeChild(breakpointMap.get(exceptionBreakpoint));
         breakpointMap.remove(exceptionBreakpoint);
      } else if(breakpoint instanceof KeYWatchpoint){
         KeYWatchpoint watchpoint = (KeYWatchpoint) breakpoint;
         breakpointStopConditions.removeChild(breakpointMap.get(watchpoint));
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
      KeYWatchpointStopCondition stopCondition = (KeYWatchpointStopCondition) breakpointMap.get(watchpoint);
      stopCondition.setEnabled(watchpoint.isEnabled());
      stopCondition.setHitCount(watchpoint.getHitCount());
      stopCondition.setConditionEnabled(watchpoint.isConditionEnabled());
      stopCondition.setCondition(watchpoint.getCondition());
      stopCondition.setSuspendOnTrue(watchpoint.isSuspendOnTrue());
   }

   /**
    * Handles the event of an existing {@link JavaExceptionBreakpoint} being changed
    * 
    * @param exceptionBreakpoint the {@link JavaExceptionBreakpoint} to be changed
    * @throws CoreException
    * @throws ProofInputException
    */
   public void exceptionBreakpointChanged(JavaExceptionBreakpoint exceptionBreakpoint) throws CoreException {
      ExceptionBreakpointStopCondition stopCondition = (ExceptionBreakpointStopCondition) breakpointMap.get(exceptionBreakpoint);
      stopCondition.setEnabled(exceptionBreakpoint.isEnabled());
      stopCondition.setCaught(exceptionBreakpoint.isCaught());
      stopCondition.setUncaught(exceptionBreakpoint.isUncaught());
      stopCondition.setSuspendOnSubclasses(exceptionBreakpoint.isSuspendOnSubclasses());
      stopCondition.setHitCount(exceptionBreakpoint.getHitCount());
   }

   /**
    * Handles the event of an existing {@link JavaLineBreakpoint} being changed
    * 
    * @param lineBreakpoint the {@link JavaLineBreakpoint} to be changed
    * @throws CoreException
    * @throws ProofInputException
    */
   public void javaLineBreakpointAdded(JavaLineBreakpoint lineBreakpoint) throws CoreException, SLTranslationException {
      LineBreakpointStopCondition stopCondition = (LineBreakpointStopCondition) breakpointMap.get(lineBreakpoint);
      stopCondition.setHitCount(lineBreakpoint.getHitCount());
      stopCondition.setEnabled(lineBreakpoint.isEnabled());
      stopCondition.setConditionEnabled(lineBreakpoint.isConditionEnabled());
      stopCondition.setCondition(lineBreakpoint.getCondition());
   }

   /**
    * Handles the event of an existing {@link JavaWatchpoint} being changed
    * 
    * @param javaWatchpoint the {@link JavaWatchpoint} to be changed
    * @throws CoreException
    * @throws ProofInputException
    */
   public void javaWatchpointChanged(JavaWatchpoint javaWatchpoint) throws CoreException {
      JavaWatchpointStopCondition stopCondition = (JavaWatchpointStopCondition) breakpointMap.get(javaWatchpoint);
      stopCondition.setHitCount(javaWatchpoint.getHitCount());
      stopCondition.setEnabled(javaWatchpoint.isEnabled());
      stopCondition.setAccess(javaWatchpoint.isAccess());
      stopCondition.setModification(javaWatchpoint.isModification());
   }

   /**
    * Handles the event of an existing {@link JavaMethodBreakpoint} being changed
    * 
    * @param methodBreakpoint the {@link JavaMethodBreakpoint} to be changed
    * @throws CoreException
    * @throws ProofInputException
    */
   public void methodBreakpointChanged(JavaMethodBreakpoint methodBreakpoint) throws CoreException, SLTranslationException {
      MethodBreakpointStopCondition stopCondition = (MethodBreakpointStopCondition) breakpointMap.get(methodBreakpoint);
      stopCondition.setHitCount(methodBreakpoint.getHitCount());
      stopCondition.setEnabled(methodBreakpoint.isEnabled());
      stopCondition.setConditionEnabled(methodBreakpoint.isConditionEnabled());
      stopCondition.setCondition(methodBreakpoint.getCondition());
      stopCondition.setEntry(methodBreakpoint.isEntry());
      stopCondition.setExit(methodBreakpoint.isExit());
   }

   /**
    * @return the breakpointStopConditions
    */
   public CompoundStopCondition getBreakpointStopConditions() {
      return breakpointStopConditions;
   }
   
   /**
    * @return the breakpointMap
    */
   public Map<IBreakpoint, IStopCondition> getBreakpointMap() {
      return breakpointMap;
   }
   
   /**
    * @param breakpointMap the breakpointMap to set
    */
   public void setBreakpointMap(Map<IBreakpoint, IStopCondition> breakpointMap) {
      this.breakpointMap = breakpointMap;
   }
}
