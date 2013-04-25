package org.key_project.sed.key.core.model;

import java.util.Iterator;
import java.util.Map;
import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaLineBreakpoint;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;

@SuppressWarnings("restriction")
public class BreakpointStopCondition implements IStopCondition {

   private Map<IPath, Vector<JavaLineBreakpoint>> breakpointLineMap;

   public BreakpointStopCondition(
         Map<IPath, Vector<JavaLineBreakpoint>> breakpointLineMap) {
      this.breakpointLineMap = breakpointLineMap;
   }

   @Override
   public int getMaximalWork(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser) {
      // TODO Auto-generated method stub
      return 0;
   }

   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      // TODO Auto-generated method stub
      return true;
   }

   @Override
   public String getGoalNotAllowedMessage(int maxApplications, long timeout,
         Proof proof, IGoalChooser goalChooser, long startTime,
         int countApplied, Goal goal) {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public boolean shouldStop(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) {
      if (singleRuleApplicationInfo != null) {
         // Get the node on which a rule was applied.
         Goal goal = singleRuleApplicationInfo.getGoal();
         Node goalNode = goal.node();
         SourceElement activeStatement = NodeInfo.computeActiveStatement(singleRuleApplicationInfo.getAppliedRuleApp());
         assert goalNode.childrenCount() == 0; // Make sure that this is the
                                               // current goal node
         if (activeStatement != null && activeStatement.getEndPosition().getLine() != -1) {
            IPath path = new Path(activeStatement.getPositionInfo().getParentClass());
            Vector<JavaLineBreakpoint> breakpointsForClass = breakpointLineMap.get(path);
            int line = activeStatement.getEndPosition().getLine();
            if (breakpointsForClass != null) {
               boolean stopConditon = classHasBreakpointInLine(breakpointsForClass, line);
               return stopConditon;
            }
         }
      }
      return false;
   }

   private boolean classHasBreakpointInLine(
         Vector<JavaLineBreakpoint> breakpointsForClass, int line) {
      Iterator<JavaLineBreakpoint> itr = breakpointsForClass.iterator();
      while (itr.hasNext()) {
         JavaLineBreakpoint breakpoint = itr.next();
         try {
            if (breakpoint.getLineNumber() == line) {
               return breakpoint.isEnabled();
            }
         }
         catch (CoreException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
      }
      return false;
   }

   @Override
   public String getStopMessage(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) {
      // TODO Auto-generated method stub
      return null;
   }

}
