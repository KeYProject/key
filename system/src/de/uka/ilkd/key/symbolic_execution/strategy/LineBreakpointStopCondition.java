package de.uka.ilkd.key.symbolic_execution.strategy;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;

/**
 * This{@link LineBreakpointStopCondition} represents a line breakpoint and is responsible to tell the debugger to stop execution when the respective
 * breakpoint is reached.
 * 
 * @author Marco Drebing
 */


public class LineBreakpointStopCondition implements IStopCondition {
   
   /**
    * The {@link IPath} of the class this {@link LineBreakpointStopCondition} is associated with.
    */
   private IPath classPath;
   
   /**
    * The line of the Breakpoint in the respective class.
    */
   private int lineNumber;
   
   /**
    * The HitCount of the Breakpoint (set by user).
    */
   private int hitCount;
   
   /**
    * Counter for how often the Breakpoint was hit.
    */
   private int hitted = 0;
   
   /**
    * The condition  for this Breakpoint (set by user).
    */
   private String condition;
   
   /**
    * The flag if the Breakpoint is enabled.
    */
   private boolean enabled;


   /**
    * Constructor to generate a new {@link LineBreakpointStopCondition} with the given parameters.
    * and their respective Hitcounts.
    * 
    * @param classPath the path of the breakpoints javaclass
    * @param lineNumber the line of the breakpoint
    * @param hitCount of the breakpoint
    * @param condition the condition the user stated for this breakpoint
    * @param enabled the flag if the breakpoint is enabled
    */
   public LineBreakpointStopCondition(IPath classPath, int lineNumber, int hitCount, String condition, boolean enabled) {
      this.classPath=classPath;
      this.lineNumber=lineNumber;
      this.hitCount=hitCount;
      this.setCondition(condition);
      this.enabled=enabled;
      // TODO: Einmalig JML-String parsen
      
      // Breakpoints
//      String className; // TODO: Defined by breakpiont
//      IProgramMethod pm = KeYUtil.getProgramMethod(IMethod, services.getJavaInfo());
//      
//      ProgramVariable selfVar = new ProgramVariable(TermBuilder.DF.newName(services, "self"), pm.sort(), pm.getType(), pm.getContainerType(), false, false, false);
//      // TODO: create paramVars like selfVar
//      PositionedString ps = new PositionedString(precondition);
//      KeYJMLParser parser = new KeYJMLParser(ps, 
//                                             services, 
//                                             getCalleeKeYJavaType(), 
//                                             selfVar, 
//                                             paramVars, 
//                                             null, 
//                                             null, 
//                                             null);
//      Term result = parser.parseExpression();
//      
//      // TODO: Im check program variablen ersetzen, key = alt, wert = neu
//      IExecutionContext ec = JavaTools.getInnermostExecutionContext(jb, services);
//      
//      Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
//      map.put(selfVar, ec.getRuntimeInstance()); // TODO arguments
//      OpReplacer replacer = new OpReplacer(map);
//      Term termForSideProof = replacer.replace(result);
//      
//      Term toProof = TermBuilder.DF.equals(TermBuilder.DF.tt(), termForSideProof);
//      ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(proof, Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(toProof), false, true));
//      boolean result = info.getProof().closed();
   }



   /**
    * {@inheritDoc}
    */
   @Override
   public int getMaximalWork(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser) {
      return 0;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getGoalNotAllowedMessage(int maxApplications, long timeout,
         Proof proof, IGoalChooser goalChooser, long startTime,
         int countApplied, Goal goal) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean shouldStop(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) {
      if (singleRuleApplicationInfo != null) {
         SourceElement activeStatement = NodeInfo.computeActiveStatement(singleRuleApplicationInfo.getAppliedRuleApp());
         if (activeStatement != null && activeStatement.getEndPosition().getLine() != -1) {
            IPath path = new Path(activeStatement.getPositionInfo().getParentClass());
            int line = activeStatement.getEndPosition().getLine();
            return shouldStopInLine(line, path);
         }
      }
      return false;
   }
   


   /**
    * Checks if the execution should stop in the given line for the given class.
    * 
    * @param line The current line of code, that the auto mode is evaluating
    * @param path The {@link IPath} of the Class, that contains the currently evaluated code 
    * @return true if a {@link JavaLineBreakpoint} is in the given line and the condition evaluates to true and the Hitcount is exceeded, false otherwise
    */
   private boolean shouldStopInLine(int line, IPath path) {
            if (lineNumber == line && classPath.equals(path)) {
               return hitcountExceeded()&&enabled;
               }
      return false;
   }

   /**
    * Checks if the Hitcount is exceeded for the given {@link JavaLineBreakpoint}.
    * If the Hitcount is not exceeded the hitted counter is incremented, otherwise its set to 0.
    * 
    * @return true if the Hitcount is exceeded or the {@link JavaLineBreakpoint} has no Hitcount.
    * @throws CoreException
    */
   private boolean hitcountExceeded(){
      if (!(hitCount == -1)) {
         if (hitCount == hitted + 1) {
            hitted=0;
            return true;
         }
         else {
           hitted++;
         }
      }
      else {
         return true;
      }
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getStopMessage(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) {
      return null;
   }

   public String getCondition() {
      return condition;
   }

   public void setCondition(String condition) {
      this.condition = condition;
   }
   
   public int getHitCount() {
      return hitCount;
   }

   public void setHitCount(int hitCount) {
      this.hitCount = hitCount;
   }
   
   public boolean isEnabled() {
      return enabled;
   }

   public void setEnabled(boolean enabled) {
      this.enabled = enabled;
   }

}
