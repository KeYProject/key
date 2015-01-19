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

package org.key_project.sed.key.core.test.util;

import java.util.LinkedHashSet;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaExceptionBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaLineBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaMethodBreakpoint;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaWatchpoint;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.proof.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.FieldWatchpoint;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.LineBreakpoint;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.MethodBreakpoint;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.SymbolicExecutionExceptionBreakpoint;

@SuppressWarnings("restriction")
public final class TestBreakpointsUtil {
   
   public static void addSomeBreakpoints(String path, SWTWorkbenchBot bot, Object... exceptions) {
      IPath callerPath = new Path(path);
      IFile callerFile = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(callerPath);
      openPerspective("Java", bot);
      TestUtilsUtil.openEditor(callerFile);
      for(Object exception : exceptions){
         if(exception instanceof Integer){
            toggleBreakpoint((Integer)exception, bot);
         }else if(exception instanceof String){
            toggleExceptionBreakpoint((String)exception, bot);
         }
      }
      openPerspective("Symbolic Debug", bot);
   }
   
   public static void removeAllBreakpoints(){
      IBreakpoint[] breakpoints = DebugPlugin.getDefault().getBreakpointManager().getBreakpoints();
      for(IBreakpoint breakpoint : breakpoints){
         try {
            breakpoint.delete();
         }
         catch (CoreException e) {
            e.printStackTrace();
         }
      }
   }
   
   public static void toggleExceptionBreakpoint(String string, SWTWorkbenchBot bot) {
      SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();
      editor.navigateTo(0, 0);
      TestUtilsUtil.menuClick(bot, "Run", "Add Java Exception Breakpoint...");
      SWTBotShell addExceptionBreakpointShell = bot.activeShell();
      addExceptionBreakpointShell.activate();
      bot.text(0).setText(string);
      SWTBotTable table = bot.table();
      while(table.rowCount()==0);
      TestUtilsUtil.sleep(100);
      TestUtilsUtil.clickDirectly(bot, "OK");
   }
   
   public static boolean removeBrakpoint(SWTWorkbenchBot bot, String breakpointTableName){
      try {
         SWTBotView view = openBreakpointView(bot);
         SWTBotTree tree = view.bot().tree();
         SWTBotTreeItem treeItem = tree.getTreeItem(breakpointTableName);
         Object treeItemData = TestUtilsUtil.getTreeItemData(treeItem);
         if(treeItemData instanceof IBreakpoint){
            IBreakpoint breakpoint = (IBreakpoint) treeItemData;
            breakpoint.delete();
            return true;
         }
      }
      catch (Exception e) {
         return false;
      }
      return false;
   }

   public static boolean changeHitCount(SWTWorkbenchBot bot, String breakpointTableName, int newHitCount){
      try {
         SWTBotView view = openBreakpointView(bot);
         SWTBotTree tree = view.bot().tree();
         SWTBotTreeItem treeItem = tree.getTreeItem(breakpointTableName);
         Object treeItemData = TestUtilsUtil.getTreeItemData(treeItem);
         if(treeItemData instanceof JavaBreakpoint){
            JavaBreakpoint breakpoint = (JavaBreakpoint) treeItemData;
            breakpoint.setHitCount(newHitCount);
            return true;
         }
      }
      catch (Exception e) {
         return false;
      }
      return false;
   }
   
   public static void openPerspective(String perspective, SWTWorkbenchBot bot){
      TestUtilsUtil.menuClick(bot, "Window", "Open Perspective", "Other...");
      SWTBotShell openPerspectiveShell  = bot.shell("Open Perspective");
      openPerspectiveShell.activate();
      bot.table().select(perspective);
      TestUtilsUtil.clickDirectly(bot, "OK");
   }
   
   public static void toggleBreakpoint(int line, SWTWorkbenchBot bot){
      SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();
      editor.navigateTo(line, 0);
      TestUtilsUtil.menuClick(bot, "Run", "Toggle Breakpoint");
   }
   
   public static Set<de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint> getBreakpointStopConditions(IStopCondition stopCondition) {
      Set<de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint>lineBreakpoints = new LinkedHashSet<de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint>();
      if(stopCondition instanceof CompoundStopCondition){
         CompoundStopCondition compoundStopCondition = (CompoundStopCondition) stopCondition;
         for(IStopCondition child : compoundStopCondition.getChildren()){
            lineBreakpoints.addAll(getBreakpointStopConditions(child));
         }
      }else if(stopCondition instanceof SymbolicExecutionBreakpointStopCondition){
         lineBreakpoints.addAll(((SymbolicExecutionBreakpointStopCondition) stopCondition).getBreakpoints());
      }
      return lineBreakpoints;
   }
   
   public static boolean checkProofContainsSomeBreakpoints(ISEDDebugTarget target,
         int numberOfLines, int numberOfExceptions, int numberOfMethods, int numberOfWatchpoints) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      IStopCondition stopCondition = keyTarget.getProof().getSettings().getStrategySettings().getCustomApplyStrategyStopCondition();
      return checkListContainsSomeBreakpoints(getBreakpointStopConditions(stopCondition), numberOfLines, numberOfExceptions, numberOfMethods, numberOfWatchpoints);
   }

   public static boolean checkTargetContainsSomeBreakpoints(ISEDDebugTarget target,
         int numberOfLines, int numberOfExceptions, int numberOfMethods, int numberOfWatchpoints) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      SymbolicExecutionBreakpointStopCondition stopCondition = keyTarget.getBreakpointStopCondition();
      return checkListContainsSomeBreakpoints(stopCondition.getBreakpoints(), numberOfLines, numberOfExceptions, numberOfMethods, numberOfWatchpoints);
   }
   
   private static boolean checkListContainsSomeBreakpoints(Set<de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint> list,
         int numberOfLines, int numberOfExceptions, int numberOfMethods, int numberOfWatchpoints){
      int localNumberOfMethods = 0;
      int localNumberOfExceptions = 0;
      int localNumberOfWatchpoints = 0;
      int localNumberOfLines = 0;
      for(de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint breakpoint : list){
         if(breakpoint instanceof MethodBreakpoint){
            localNumberOfMethods++;
         } 
         else if(breakpoint instanceof FieldWatchpoint){
            localNumberOfWatchpoints++;
         } 
         else if(breakpoint instanceof SymbolicExecutionExceptionBreakpoint){
            localNumberOfExceptions++;
         } 
         else if(breakpoint instanceof LineBreakpoint){
            localNumberOfLines++;
         }
      }
      return numberOfLines==localNumberOfLines
            &&numberOfExceptions==localNumberOfExceptions
            &&numberOfMethods==localNumberOfMethods
            &&numberOfWatchpoints==localNumberOfWatchpoints;
   }

   public static boolean checkTargetHitCountofAllBreakpoints(
         ISEDDebugTarget target, int hitCount) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      SymbolicExecutionBreakpointStopCondition stopCondition = keyTarget.getBreakpointStopCondition();
      return checkListHitCountOfAllBreakpoints(stopCondition.getBreakpoints(), hitCount);
   }

   public static boolean checkProofHitCountofAllBreakpoints(
         ISEDDebugTarget target, int hitCount) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      IStopCondition stopCondition = keyTarget.getProof().getSettings().getStrategySettings().getCustomApplyStrategyStopCondition();
      return checkListHitCountOfAllBreakpoints(getBreakpointStopConditions(stopCondition), hitCount);
   }

   private static boolean checkListHitCountOfAllBreakpoints(
         Set<de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint> list, int hitCount) {
      for(de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint breakpoint : list){
         if(breakpoint instanceof MethodBreakpoint){
            if(!(((MethodBreakpoint)breakpoint).getHitCount()==hitCount)){
               return false;
            }
         } 
         else if(breakpoint instanceof FieldWatchpoint){
            if(!(((FieldWatchpoint)breakpoint).getHitCount()==hitCount)){
               return false;
            }
         } 
         else if(breakpoint instanceof SymbolicExecutionExceptionBreakpoint){
            if(!(((SymbolicExecutionExceptionBreakpoint)breakpoint).getHitCount()==hitCount)){
               return false;
            }
         } 
         else if(breakpoint instanceof LineBreakpoint){
            if(!(((LineBreakpoint)breakpoint).getHitCount()==hitCount)){
               return false;
            }
         }
      }
      return true;
   }

   public static boolean changeEnabled(SWTWorkbenchBot bot, String breakpointTableName,
         boolean enabled) {
      try {
         SWTBotView view = openBreakpointView(bot);
         SWTBotTree tree = view.bot().tree();
         SWTBotTreeItem treeItem = tree.getTreeItem(breakpointTableName);
         Object treeItemData = TestUtilsUtil.getTreeItemData(treeItem);
         if(treeItemData instanceof JavaBreakpoint){
            JavaBreakpoint breakpoint = (JavaBreakpoint) treeItemData;
            breakpoint.setEnabled(enabled);
            return true;
         }
      }
      catch (Exception e) {
         return false;
      }
      return false;
   }

   public static boolean checkTargetEnabledofAllBreakpoints(
         ISEDDebugTarget target, boolean enabled) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      SymbolicExecutionBreakpointStopCondition stopCondition = keyTarget.getBreakpointStopCondition();
      return checkListEnabledOfAllBreakpoints(stopCondition.getBreakpoints(), enabled);
   }

   public static boolean checkProofEnabledofAllBreakpoints(
         ISEDDebugTarget target, boolean enabled) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      IStopCondition stopCondition = keyTarget.getProof().getSettings().getStrategySettings().getCustomApplyStrategyStopCondition();
      return checkListEnabledOfAllBreakpoints(getBreakpointStopConditions(stopCondition), enabled);
   }

   private static boolean checkListEnabledOfAllBreakpoints(
         Set<de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint> list, boolean enabled) {
      for(de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint breakpoint : list){
         if(breakpoint instanceof MethodBreakpoint){
            if(!(((MethodBreakpoint)breakpoint).isEnabled()==enabled)){
               return false;
            }
         } 
         else if(breakpoint instanceof FieldWatchpoint){
            if(!(((FieldWatchpoint)breakpoint).isEnabled()==enabled)){
               return false;
            }
         } 
         else if(breakpoint instanceof SymbolicExecutionExceptionBreakpoint){
            if(!(((SymbolicExecutionExceptionBreakpoint)breakpoint).isEnabled()==enabled)){
               return false;
            }
         } 
         else if(breakpoint instanceof LineBreakpoint){
            if(!(((LineBreakpoint)breakpoint).isEnabled()==enabled)){
               return false;
            }
         }
      }
      return true;
   }

   public static boolean changeCondition(SWTWorkbenchBot bot, String breakpointTableName,
         String condition) {
      try {
         SWTBotView view = openBreakpointView(bot);
         SWTBotTree tree = view.bot().tree();
         SWTBotTreeItem treeItem = tree.getTreeItem(breakpointTableName);
         Object treeItemData = TestUtilsUtil.getTreeItemData(treeItem);
         if(treeItemData instanceof JavaLineBreakpoint){
            JavaLineBreakpoint breakpoint = (JavaLineBreakpoint) treeItemData;
            breakpoint.setConditionEnabled(true);
            breakpoint.setCondition(condition);
            return true;
         }
      }
      catch (Exception e) {
         return false;
      }
      return false;
   }

   public static boolean checkTargetConditiondofAllBreakpoints(
         ISEDDebugTarget target, String condition, boolean enabled) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      SymbolicExecutionBreakpointStopCondition stopCondition = keyTarget.getBreakpointStopCondition();
      return checkListConditionOfAllBreakpoints(stopCondition.getBreakpoints(), condition, enabled);
   }

   public static boolean checkProofConditionofAllBreakpoints(
         ISEDDebugTarget target, String condition, boolean enabled) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      IStopCondition stopCondition = keyTarget.getProof().getSettings().getStrategySettings().getCustomApplyStrategyStopCondition();
      return checkListConditionOfAllBreakpoints(getBreakpointStopConditions(stopCondition), condition, enabled);
   }

   private static boolean checkListConditionOfAllBreakpoints(
         Set<de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint> list, String condition,
         boolean enabled) {
      for(de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint breakpoint : list){
         if(breakpoint instanceof MethodBreakpoint){
            String localCondition = ((MethodBreakpoint)breakpoint).getConditionString();
            if(localCondition==null){
               if(!(condition==null)){
                  return false;
               }
            }else{
               if(!localCondition.equals(condition)){
                  return false;
               }
            }
            if(!(((MethodBreakpoint)breakpoint).isConditionEnabled()==enabled)){
               return false;
            }
         } 
         else if(breakpoint instanceof LineBreakpoint){
            if(!(((LineBreakpoint)breakpoint).isConditionEnabled()==enabled)){
               String localCondition = ((LineBreakpoint)breakpoint).getConditionString();
               if(localCondition==null){
                  if(!(condition==null)){
                     return false;
                  }
               }else{
                  if(!localCondition.equals(condition)){
                     return false;
                  }
                  if(!(((LineBreakpoint)breakpoint).isConditionEnabled()==enabled)){
                     return false;
                  }
               }
            }
         }
      }
      return true;
   }

   public static boolean changeAccessAndModification(SWTWorkbenchBot bot,
         String breakpointTableName, boolean access, boolean modification) {
      try {
         SWTBotView view = openBreakpointView(bot);
         SWTBotTree tree = view.bot().tree();
         SWTBotTreeItem treeItem = tree.getTreeItem(breakpointTableName);
         Object treeItemData = TestUtilsUtil.getTreeItemData(treeItem);
         if(treeItemData instanceof JavaWatchpoint){
            JavaWatchpoint breakpoint = (JavaWatchpoint) treeItemData;
            breakpoint.setAccess(access);
            breakpoint.setModification(modification);
            return true;
         }
      }
      catch (Exception e) {
         return false;
      }
         return false;
   }
   
   public static SWTBotView openBreakpointView(SWTWorkbenchBot bot) throws Exception {
      TestUtilsUtil.openView(IDebugUIConstants.ID_BREAKPOINT_VIEW);
      return bot.viewById(IDebugUIConstants.ID_BREAKPOINT_VIEW);
   }

   public static boolean changeEntryAndExit(SWTWorkbenchBot bot,
         String breakpointTableName, boolean entry, boolean exit) {
      try {
         SWTBotView view = openBreakpointView(bot);
         SWTBotTree tree = view.bot().tree();
         SWTBotTreeItem treeItem = tree.getTreeItem(breakpointTableName);
         Object treeItemData = TestUtilsUtil.getTreeItemData(treeItem);
         if(treeItemData instanceof JavaMethodBreakpoint){
            JavaMethodBreakpoint breakpoint = (JavaMethodBreakpoint) treeItemData;
               breakpoint.setEntry(entry);
               breakpoint.setExit(exit);
               return true;
         }
      }
      catch (Exception e) {
         return false;
      }
         return false;
      }

   public static boolean checkTargetAccessAndModificationofAllBreakpoints(
         ISEDDebugTarget target, int numberOfAccesses, int numberOfModifications) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      SymbolicExecutionBreakpointStopCondition stopCondition = keyTarget.getBreakpointStopCondition();
      return checkListAccessAndModificationofAllBreakpoints(stopCondition.getBreakpoints(), numberOfAccesses, numberOfModifications);
   }

   public static boolean checkProofAccessAndModificationofAllBreakpoints(
         ISEDDebugTarget target, int numberOfAccesses, int numberOfModifications) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      IStopCondition stopCondition = keyTarget.getProof().getSettings().getStrategySettings().getCustomApplyStrategyStopCondition();
      return checkListAccessAndModificationofAllBreakpoints(getBreakpointStopConditions(stopCondition), numberOfAccesses, numberOfModifications);
   }

   private static boolean checkListAccessAndModificationofAllBreakpoints(
         Set<de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint> list, int numberOfAccesses,
         int numberOfModifications) {
      int localNumberOfAccesses = 0;
      int localNumberOfModifications = 0;
      for(de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint breakpoint : list){
         if(breakpoint instanceof FieldWatchpoint){
            FieldWatchpoint watchpoint = (FieldWatchpoint)breakpoint;
            if(watchpoint.isAccess()){
               localNumberOfAccesses++;
            }
            if(watchpoint.isModification()){
               localNumberOfModifications++;
            }
         } 
      }
      return numberOfAccesses==localNumberOfAccesses
            &&numberOfModifications==localNumberOfModifications;
   }

   public static boolean checkProofEntryAndExitofAllBreakpoints(
         ISEDDebugTarget target, int entries, int exits) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      IStopCondition stopCondition = keyTarget.getProof().getSettings().getStrategySettings().getCustomApplyStrategyStopCondition();
      return checkListEntryAndExitofAllBreakpoints(getBreakpointStopConditions(stopCondition), entries, exits);
   }

   public static boolean checkTargetEntryAndExitofAllBreakpoints(
         ISEDDebugTarget target, int entries, int exits) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      SymbolicExecutionBreakpointStopCondition stopCondition = keyTarget.getBreakpointStopCondition();
      return checkListEntryAndExitofAllBreakpoints(stopCondition.getBreakpoints(), entries, exits);
   }

   private static boolean checkListEntryAndExitofAllBreakpoints(
         Set<de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint> list, int numberOfEntries,
         int numberOfExits) {
      int localNumberOfEntries = 0;
      int localNumberOfExits = 0;
      for(de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint breakpoint : list){
         if(breakpoint instanceof MethodBreakpoint){
            MethodBreakpoint methodBreakpoint = (MethodBreakpoint)breakpoint;
            if(methodBreakpoint.isEntry()){
               localNumberOfEntries++;
            }
            if(methodBreakpoint.isExit()){
               localNumberOfExits++;
            }
         } 
      }
      return numberOfEntries==localNumberOfEntries
            &&numberOfExits==localNumberOfExits;
   }

   public static boolean changeCaughtUncaughtSubclass(SWTWorkbenchBot bot,
         String breakpointTableName, boolean caught, boolean uncaught, boolean subclass) {
      try {
         SWTBotView view = openBreakpointView(bot);
         SWTBotTree tree = view.bot().tree();
         SWTBotTreeItem treeItem = tree.getTreeItem(breakpointTableName);
         Object treeItemData = TestUtilsUtil.getTreeItemData(treeItem);
         if(treeItemData instanceof JavaExceptionBreakpoint){
            JavaExceptionBreakpoint exceptionBreakpoint = (JavaExceptionBreakpoint) treeItemData;
            exceptionBreakpoint.setSuspendOnSubclasses(subclass);
            exceptionBreakpoint.setCaught(caught);
            exceptionBreakpoint.setUncaught(uncaught);
            return true;
         }
      }
      catch (Exception e) {
         return false;
      }
         return false;
   }

   public static boolean checkTargetCaughtUncaughtSubclass(
         ISEDDebugTarget target, int numberOfCaught, int numberOfUncaught, int numberOfSubclass) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      SymbolicExecutionBreakpointStopCondition stopCondition = keyTarget.getBreakpointStopCondition();
      return checkListCaughtUncaughtSubclassofAllBreakpoints(stopCondition.getBreakpoints(), numberOfCaught, numberOfUncaught, numberOfSubclass);
   }

   private static boolean checkListCaughtUncaughtSubclassofAllBreakpoints(
         Set<de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint> list, int numberOfCaught,
         int numberOfUncaught, int numberOfSubclass) {
      int localNumberOfCaught = 0;
      int localNumberOfUncaught = 0;
      int localNumberOfSubclass = 0;
      for(de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint breakpoint : list){
         if(breakpoint instanceof SymbolicExecutionExceptionBreakpoint){
            SymbolicExecutionExceptionBreakpoint exceptionBreakpoint = (SymbolicExecutionExceptionBreakpoint)breakpoint;
            if(exceptionBreakpoint.isCaught()){
               localNumberOfCaught++;
            }
            if(exceptionBreakpoint.isUncaught()){
               localNumberOfUncaught++;
            }
            if(exceptionBreakpoint.isSuspendOnSubclasses()){
               localNumberOfSubclass++;
            }
         } 
      }
      return numberOfCaught==localNumberOfCaught
            &&numberOfUncaught==localNumberOfUncaught
            &&numberOfSubclass==localNumberOfSubclass;
   }

   public static boolean checkProofCaughtUncaughtSubclass(
         ISEDDebugTarget target, int numberOfCaught, int numberOfUncaught, int numberOfSubclass) {
      KeYDebugTarget keyTarget = (KeYDebugTarget)target;
      IStopCondition stopCondition = keyTarget.getProof().getSettings().getStrategySettings().getCustomApplyStrategyStopCondition();
      return checkListCaughtUncaughtSubclassofAllBreakpoints(getBreakpointStopConditions(stopCondition), numberOfCaught, numberOfUncaught, numberOfSubclass);
   }
}