package org.key_project.sed.key.core.test.testcase.swtbot;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.LineBreakpointStopCondition;

public class SWTBotBreakpointTestCase extends AbstractKeYDebugTargetTestCase {
   
   private static final String CALLER_PATH= ResourcesPlugin.getWorkspace().getRoot().getRawLocation().toString() + "/SWTBotBreakpointTestCase_testLineBreakpoints/src/BreakpointStopCaller.java";
   
   private static final String CALLEE_PATH=ResourcesPlugin.getWorkspace().getRoot().getRawLocation().toString() + "/SWTBotBreakpointTestCase_testLineBreakpoints/src/BreakpointStopCallee.java";
   
   @Test
   public void testLineBreakpoints() throws Exception{
      IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
         @Override
         public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
            KeYDebugTarget keyTarget = (KeYDebugTarget)target;
            // Get debug target TreeItem
               SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
               IPath callerPath = new Path(ResourcesPlugin.getWorkspace().getRoot().getRawLocation().toString() + "/SWTBotBreakpointTestCase_testLineBreakpoints/src/BreakpointStopCaller.java");
               IPath calleePath = new Path(ResourcesPlugin.getWorkspace().getRoot().getRawLocation().toString() + "/SWTBotBreakpointTestCase_testLineBreakpoints/src/BreakpointStopCallee.java");
               IFile callerFile = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(callerPath);
               IFile calleeFile = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(calleePath);
               openPerspective("Java", bot);
               TestUtilsUtil.openEditor(callerFile);
               toggleBreakpoint(15, bot);
               toggleBreakpoint(9, bot);
               TestUtilsUtil.openEditor(calleeFile);
               toggleBreakpoint(5, bot);
               openPerspective("Symbolic Debug", bot);
               
               
               
               SWTBotView view = TestUtilsUtil.openView(bot, "Debug", "Breakpoints");
               view.bot().tree().setFocus();
               SWTBotTreeItem treeItem = TestUtilsUtil.selectInTree(view.bot().tree(), "BreakpointStopCallee [line: 6] - main(int)");
               
               treeItem.contextMenu("Disable");
               
               resume(bot, item, target);
               
               
               IStopCondition stopCondition = keyTarget.getProof().getSettings().getStrategySettings().getCustomApplyStrategyStopCondition();
               
               List<LineBreakpointStopCondition>lineBreakpoints = getLineBreakpointStopConditions(stopCondition);
               
               for(LineBreakpointStopCondition lineBreakpoint : lineBreakpoints){
                  if(lineBreakpoint.getLineNumber()==10 && lineBreakpoint.getClassPath().toString().equals(CALLER_PATH)){
                     assertEquals(lineBreakpoint.getLineNumber(), 10);
                     assertEquals(lineBreakpoint.getClassPath().toString(), CALLER_PATH);
                  }
                  else if(lineBreakpoint.getLineNumber()==16 && lineBreakpoint.getClassPath().toString().equals(CALLER_PATH)){
                     assertEquals(lineBreakpoint.getLineNumber(), 16);
                     assertEquals(lineBreakpoint.getClassPath().toString(), CALLER_PATH);
                  }
                  else if(lineBreakpoint.getLineNumber()==6 && lineBreakpoint.getClassPath().toString().equals(CALLEE_PATH)){
                     assertEquals(lineBreakpoint.getLineNumber(), 6);
                     assertEquals(lineBreakpoint.getClassPath().toString(), CALLEE_PATH);
                     
                  }
                  else{
                     TestCase.fail("Unknown Breakpoint found");
                  }
               }
         }
      };
      doKeYDebugTargetTest("SWTBotBreakpointTestCase_testLineBreakpoints",
            "data/BreakpointTest/test",
            true,
            true,
            createMethodSelector("BreakpointStopCaller", "main"),
            null,
            null,
            Boolean.FALSE,
            Boolean.FALSE,
            Boolean.FALSE,
            Boolean.FALSE,
            8,
            executor);   
   
   }
   
   private void openPerspective(String perspective, SWTWorkbenchBot bot){
      TestUtilsUtil.menuClick(bot, "Window", "Open Perspective", "Other...");
      SWTBotShell openPerspectiveShell  = bot.shell("Open Perspective");
      openPerspectiveShell.activate();
      bot.table().select(perspective);
      TestUtilsUtil.clickDirectly(bot, "OK");
   }
   
   private void toggleBreakpoint(int line, SWTWorkbenchBot bot){
      SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();
      editor.navigateTo(line, 0);
      TestUtilsUtil.menuClick(bot, "Run", "Toggle Breakpoint");
   }
   
   private List<LineBreakpointStopCondition> getLineBreakpointStopConditions(IStopCondition stopCondition) {
      List<LineBreakpointStopCondition>lineBreakpoints = new ArrayList<LineBreakpointStopCondition>();
      if(stopCondition instanceof CompoundStopCondition){
         CompoundStopCondition compoundStopCondition = (CompoundStopCondition) stopCondition;
         for(IStopCondition child : compoundStopCondition.getChildren()){
            lineBreakpoints.addAll(getLineBreakpointStopConditions(child));
         }
      }else if(stopCondition instanceof LineBreakpointStopCondition){
         lineBreakpoints.add((LineBreakpointStopCondition) stopCondition);
      }
      return lineBreakpoints;
   }

}
