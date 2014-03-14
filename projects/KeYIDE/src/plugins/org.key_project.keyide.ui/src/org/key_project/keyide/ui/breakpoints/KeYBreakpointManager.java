package org.key_project.keyide.ui.breakpoints;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.IBreakpointListener;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaClassPrepareBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaExceptionBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaLineBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaMethodBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaWatchpoint;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Services.ITermProgramVariableCollectorFactory;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.proof.TermProgramVariableCollectorKeepUpdatesForBreakpointconditions;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.strategy.ExceptionBreakpointNonSymbolicStopCondition;
import de.uka.ilkd.key.strategy.JavaWatchpointNonSymbolicStopCondition;
import de.uka.ilkd.key.strategy.LineBreakpointNonSymbolicStopCondition;
import de.uka.ilkd.key.strategy.MethodBreakpointNonSymbolicStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

@SuppressWarnings("restriction")
public class KeYBreakpointManager implements IBreakpointListener {
   /**
    * The {@link CompoundStopCondition} that holds all BreakpointsStopCOnditons for this {@link KeYDebugTarget}.
    */
   private CompoundStopCondition breakpointStopConditions = new CompoundStopCondition();

   /**
    * The Map of {@link JavaLineBreakpoint}s with their current HitCount as value.
    */
   private Map<IBreakpoint, IStopCondition> breakpointMap;
   
   private KeYEnvironment<?> environment;
   
   private Proof proof;
   
   /**
    * Creates a new {@link KeYBreakpointManager}
    */
   public KeYBreakpointManager(KeYEnvironment<?> environment, Proof proof){
      breakpointMap = new HashMap<IBreakpoint, IStopCondition>();
      this.environment=environment;
      this.proof = proof;
      addBreakpoints();
   }
   
   
   /**
    * Adds all Breakpoints to this DebugTarget. Is called only when the DebugTarget is initially created.
    */
   private void addBreakpoints(){ 
      IBreakpoint[] breakpoints = DebugPlugin.getDefault().getBreakpointManager().getBreakpoints();      
      for(int i = 0; i < breakpoints.length; i++){
         breakpointAdded(breakpoints[i]);
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
   public void methodBreakpointAdded(JavaMethodBreakpoint methodBreakpoint) throws CoreException, ProofInputException {
      IResource resource = methodBreakpoint.getMarker().getResource();
      if (resource.getFileExtension() != null && resource.getFileExtension().equalsIgnoreCase("java")) {
         IMethod method = KeYUtil.getContainingMethodForMethodStart(methodBreakpoint.getCharStart(), resource);
         // Determine container type
         IType containerType = method.getDeclaringType();
         String containerTypeName = containerType.getFullyQualifiedName();
         containerTypeName = containerTypeName.replace('$', '.'); // Inner and anonymous classes are separated with '.' instead of '$' in KeY
         KeYJavaType containerKJT = proof.getJavaInfo().getTypeByClassName(containerTypeName);
         if(containerKJT!=null){
            IProgramMethod pm = KeYUtil.getProgramMethod(method, proof.getJavaInfo());
            int start = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset());
            int end = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset() + method.getSourceRange().getLength());
            MethodBreakpointNonSymbolicStopCondition stopCondition = new MethodBreakpointNonSymbolicStopCondition(
                  methodBreakpoint.getMarker().getResource().getLocation().toOSString(),
                  methodBreakpoint.getLineNumber(),
                  methodBreakpoint.getHitCount(), pm, proof,
                        methodBreakpoint.getCondition(), methodBreakpoint.isEnabled(),
                        methodBreakpoint.isConditionEnabled(), start, end, methodBreakpoint.isEntry(), methodBreakpoint.isExit());
            breakpointStopConditions.addChildren(stopCondition);
            breakpointMap.put(methodBreakpoint, stopCondition);
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
   public void javaWatchpointAdded(JavaWatchpoint javaWatchpoint) throws CoreException, ProofInputException {
      IResource resource = javaWatchpoint.getMarker().getResource();
      if (resource.getFileExtension() != null && resource.getFileExtension().equalsIgnoreCase("java")) {
         JavaInfo javaInfo = environment.getServices().getJavaInfo();
         String containerTypeName = KeYUtil.getType(resource).getFullyQualifiedName();
         containerTypeName = containerTypeName.replace('$', '.'); // Inner and anonymous classes are separated with '.' instead of '$' in KeY
         KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
         if(containerKJT!=null){
            JavaWatchpointNonSymbolicStopCondition stopCondition = new JavaWatchpointNonSymbolicStopCondition(javaWatchpoint.isEnabled(),javaWatchpoint.getHitCount(),
                  javaWatchpoint.getFieldName(), javaWatchpoint.isAccess(), javaWatchpoint.isModification(), containerKJT,
                  proof);
      breakpointStopConditions.addChildren(stopCondition);
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
   public void exceptionBreakpointAdded(JavaExceptionBreakpoint exceptionBreakpoint) throws CoreException {
      ExceptionBreakpointNonSymbolicStopCondition stopCondition = new ExceptionBreakpointNonSymbolicStopCondition(proof, exceptionBreakpoint.getTypeName(),
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
   public void lineBreakpointAdded(JavaLineBreakpoint lineBreakpoint) throws CoreException, ProofInputException {
      IResource resource = lineBreakpoint.getMarker().getResource();
      if (resource.getFileExtension() != null && resource.getFileExtension().equalsIgnoreCase("java")) {
         IMethod method = KeYUtil.getContainingMethod(lineBreakpoint.getLineNumber(), resource);
         // Determine container type
         IType containerType = method.getDeclaringType();
         String containerTypeName = containerType.getFullyQualifiedName();
         containerTypeName = containerTypeName.replace('$', '.'); // Inner and anonymous classes are separated with '.' instead of '$' in KeY
         KeYJavaType containerKJT = proof.getJavaInfo().getTypeByClassName(containerTypeName);
         if(containerKJT!=null){
            IProgramMethod pm = KeYUtil.getProgramMethod(method, proof.getJavaInfo());
            int start = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset());
            int end = KeYUtil.getLineNumberOfMethod(method, method.getSourceRange().getOffset() + method.getSourceRange().getLength());
            LineBreakpointNonSymbolicStopCondition stopCondition = new LineBreakpointNonSymbolicStopCondition(
                  resource.getLocation().toOSString(),
                  lineBreakpoint.getLineNumber(),
                  lineBreakpoint.getHitCount(), pm, proof,
                  lineBreakpoint.getCondition(), lineBreakpoint.isEnabled(),
                  lineBreakpoint.isConditionEnabled(), start, end);
            breakpointStopConditions.addChildren(stopCondition);
            breakpointMap.put(lineBreakpoint, stopCondition);
         }
      }
      
   }

   /**
    * Handles the event of a breakpoint being removed from a {@link KeYDebugTarget}.
    * 
    * @param breakpoint that is being removed
    * @param delta the associated marker delta, or null when the breakpoint is removed from the breakpoint manager without being deleted
    */
   public void breakpointRemovedInternal(IBreakpoint breakpoint, IMarkerDelta delta) {
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
      ExceptionBreakpointNonSymbolicStopCondition stopCondition = (ExceptionBreakpointNonSymbolicStopCondition) breakpointMap.get(exceptionBreakpoint);
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
   public void javaLineBreakpointChanged(JavaLineBreakpoint lineBreakpoint) throws CoreException, SLTranslationException {
      LineBreakpointNonSymbolicStopCondition stopCondition = (LineBreakpointNonSymbolicStopCondition) breakpointMap.get(lineBreakpoint);
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
      JavaWatchpointNonSymbolicStopCondition stopCondition = (JavaWatchpointNonSymbolicStopCondition) breakpointMap.get(javaWatchpoint);
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
      MethodBreakpointNonSymbolicStopCondition stopCondition = (MethodBreakpointNonSymbolicStopCondition) breakpointMap.get(methodBreakpoint);
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
   @Override
   public void breakpointAdded(IBreakpoint breakpoint) {
      try {
         if (breakpoint instanceof JavaWatchpoint) {
            JavaWatchpoint watchpoint = (JavaWatchpoint) breakpoint;
            javaWatchpointAdded(watchpoint);
         }
         else if (breakpoint instanceof JavaExceptionBreakpoint) {
            JavaExceptionBreakpoint exceptionBreakpoint = (JavaExceptionBreakpoint) breakpoint;
            exceptionBreakpointAdded(exceptionBreakpoint);
         } 
         else if (breakpoint instanceof JavaMethodBreakpoint) {
            JavaMethodBreakpoint methodBreakpoint = (JavaMethodBreakpoint) breakpoint;
            methodBreakpointAdded(methodBreakpoint);
         }
         else if (breakpoint instanceof JavaLineBreakpoint) {
            JavaLineBreakpoint lineBreakpoint = (JavaLineBreakpoint) breakpoint;
            lineBreakpointAdded(lineBreakpoint);
         }
      }
      catch (CoreException e) {
         //TODO
      }
      catch (ProofInputException e) {
         //TODO
      }
      catch(TermCreationException e){
         //TODO
      }
   }

   @Override
   public void breakpointRemoved(IBreakpoint breakpoint, IMarkerDelta delta) {
      breakpointRemovedInternal(breakpoint, delta);
   }

   @Override
   public void breakpointChanged(IBreakpoint breakpoint, IMarkerDelta delta) {
      if(delta!=null){
         try {
            if (breakpoint instanceof JavaMethodBreakpoint) {
               JavaMethodBreakpoint methodBreakpoint = (JavaMethodBreakpoint) breakpoint;
               if (this.getBreakpointMap().containsKey(methodBreakpoint)) {
                  this.methodBreakpointChanged(methodBreakpoint);
               }
               else {
                  breakpointAdded(methodBreakpoint);
               }
            }
            else if (breakpoint instanceof JavaWatchpoint) {
               JavaWatchpoint javaWatchpoint = (JavaWatchpoint) breakpoint;
               if (this.getBreakpointMap().containsKey(javaWatchpoint)) {
                  this.javaWatchpointChanged(javaWatchpoint);
               }
               else {
                  breakpointAdded(javaWatchpoint);
               }
            }
            else if (breakpoint instanceof JavaLineBreakpoint) {
               JavaLineBreakpoint lineBreakpoint = (JavaLineBreakpoint) breakpoint;
               if (this.getBreakpointMap().containsKey(lineBreakpoint)) {
                  this.javaLineBreakpointChanged(lineBreakpoint);
               }
               else {
                  breakpointAdded(lineBreakpoint);
               }
            }
            else if (breakpoint instanceof JavaExceptionBreakpoint) {
               JavaExceptionBreakpoint exceptionBreakpoint = (JavaExceptionBreakpoint) breakpoint;
               if (this.getBreakpointMap().containsKey(exceptionBreakpoint)) {
                  this.exceptionBreakpointChanged(exceptionBreakpoint);
               }
               else {
                  breakpointAdded(exceptionBreakpoint);
               }
            }
         }
         catch (CoreException e) {
            //TODO
         }
         catch (ProofInputException e) {
            //TODO
         }
         catch (TermCreationException e) {
            //TODO
         }
      }
   }


   /**
    * creates a new factory that should be used by others afterwards
    * @return 
    */
   public static ITermProgramVariableCollectorFactory createNewFactory(final CompoundStopCondition breakpointParentStopCondition) {
      ITermProgramVariableCollectorFactory programVariableCollectorFactory = new ITermProgramVariableCollectorFactory() {
         @Override
         public TermProgramVariableCollector create(Services services) {
            TermProgramVariableCollectorKeepUpdatesForBreakpointconditions collector = new TermProgramVariableCollectorKeepUpdatesForBreakpointconditions(services, breakpointParentStopCondition);
            
              return collector;
         }
      };
      return programVariableCollectorFactory;
   }

}
