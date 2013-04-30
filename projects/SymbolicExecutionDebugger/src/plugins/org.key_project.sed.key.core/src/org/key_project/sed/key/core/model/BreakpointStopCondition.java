package org.key_project.sed.key.core.model;

import java.util.ArrayList;
import java.util.Map;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaLineBreakpoint;
import org.key_project.sed.core.util.LogUtil;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.ComparativeOperator;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.metaconstruct.EvaluateArgs;

@SuppressWarnings("restriction")
public class BreakpointStopCondition implements IStopCondition {

   private Map<JavaLineBreakpoint, Integer> breakpointMap;

   public BreakpointStopCondition(Map<JavaLineBreakpoint, Integer> breakpointMap) {
      this.breakpointMap = breakpointMap;
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
            int line = activeStatement.getEndPosition().getLine();
            
//            
//            ComparativeOperator expr = new Equals(new IntLiteral(5), new IntLiteral(5));
//            EvaluateArgs evaluator = new EvaluateArgs(expr);
//            ProgramVariable pv= evaluator.evaluate(expr, new ArrayList(), proof.env().getInitialServices(), null);
//            
            
            return shouldStopInLine(line, path);
         }
      }
      return false;
   }

   private boolean shouldStopInLine(int line, IPath path) {
      for(Map.Entry<JavaLineBreakpoint, Integer> entry : breakpointMap.entrySet()) {
         try {
            if (entry.getKey().getLineNumber() == line && path.equals(entry.getKey().getMarker().getResource().getLocation())) {
               return hitcountExceeded(entry.getKey(), entry.getValue());
            }
         }
         catch (CoreException e) {
            LogUtil.getLogger().logError(e);
         }
      }
      return false;
   }

   private boolean hitcountExceeded(JavaLineBreakpoint breakpoint, int hitted) throws CoreException {
      if (!(breakpoint.getHitCount() == -1)) {
         if (breakpoint.getHitCount() == hitted + 1) {
            breakpointMap.put(breakpoint, 0);
            return breakpoint.isEnabled();
         }
         else {
            breakpointMap.put(breakpoint, hitted + 1);
         }
      }
      else {
         return breakpoint.isEnabled();
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
