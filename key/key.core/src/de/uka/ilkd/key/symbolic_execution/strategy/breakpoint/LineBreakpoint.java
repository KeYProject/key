// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.strategy.breakpoint;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.ExtList;

public class LineBreakpoint extends AbstractConditionalBreakpoint {
   /**
    * The path of the class this {@link LineBreakpoint} is associated with.
    */
   private String classPath;
   
   /**
    * The line of the Breakpoint in the respective class.
    */
   private int lineNumber;
   
   /**
    * The start of the method containing the associated Breakpoint
    */
   protected int methodStart;
  
   /**
    * The end of the method containing the associated Breakpoint
    */
   protected int methodEnd;

   /**
    * Creates a new {@link LineBreakpoint}.
    * 
    * @param classPath the path of the class the associated Breakpoint lies within
    * @param lineNumber the line where the associated Breakpoint is located in the class
    * @param hitCount the number of hits after which the execution should hold at this breakpoint
    * @param pm the {@link IProgramMethod} representing the Method which the Breakpoint is located at
    * @param proof the {@link Proof} that will be executed and should stop
    * @param condition the condition as given by the user
    * @param enabled flag if the Breakpoint is enabled
    * @param conditionEnabled flag if the condition is enabled
    * @param methodStart the line the containing method of this breakpoint starts at
    * @param methodEnd the line the containing method of this breakpoint ends at
    * @throws SLTranslationException if the condition could not be parsed to a valid Term
    */
   public LineBreakpoint(String classPath, int lineNumber, int hitCount, IProgramMethod pm, Proof proof, String condition, boolean enabled, boolean conditionEnabled, int methodStart, int methodEnd) throws SLTranslationException {
      super(hitCount, pm, proof,  enabled, conditionEnabled, methodStart, methodEnd, pm.getContainerType());
      this.classPath=classPath;
      this.methodEnd=methodEnd;
      this.methodStart=methodStart;
      this.lineNumber=lineNumber;
      this.setCondition(condition);
   }

  

   /**
    * For a given {@link StatementContainer} this method computes the {@link StatementBlock} that contains all lines before the line the Breakpoint is at, including the line itself.
    * 
    * @param statementContainer the {@link StatementContainer} to build the block from
    * @return the {@link StatementBlock} representing the container without the line below the Breakpoint
    */
   @Override
   protected StatementBlock getStatementBlock(StatementContainer statementContainer) {
      //list of all statements
      ExtList nextResult=new ExtList();
      for(int i = 0; i<statementContainer.getStatementCount();i++){
         nextResult.add(statementContainer.getStatementAt(i));
      }
      //find last interesting statement
      for(int i = 0;i<nextResult.size();i++){
         if(!(((SourceElement) nextResult.get(i)).getEndPosition().getLine()<=lineNumber)){
            if(nextResult.get(i) instanceof StatementContainer){
               //go into inner scope
               nextResult.set(i, getStatementBlock((StatementContainer)nextResult.get(i)));
            }else{
               //cut below last interesting statement
               for(int j = nextResult.size()-1;j>=i;j--){
                  nextResult.remove(statementContainer.getChildAt(j));
               }
            }
         }
      }
      return new StatementBlock(nextResult);
   }

   /**
    * Checks if the execution should stop in the given line for the given class.
    * 
    * @param line The current line of code, that the auto mode is evaluating
    * @param path The path of the Class, that contains the currently evaluated code 
    * @return true if a {@link JavaLineBreakpoint} is in the given line and the condition evaluates to true and the Hitcount is exceeded, false otherwise
    */
   protected boolean shouldStopInLine(int line, String path) {
      if (lineNumber == line && getClassPath().equals(path)) {
         return true;
      }
      return false;
   }
   
   @Override
   public boolean isBreakpointHit(SourceElement activeStatement, RuleApp ruleApp, Proof proof, Node node) {
      return isInLine(activeStatement)&&super.isBreakpointHit(activeStatement, ruleApp, proof, node);
   }
   
   private boolean isInLine(SourceElement activeStatement){
      if (activeStatement != null && activeStatement.getStartPosition() != Position.UNDEFINED) {
         String path = activeStatement.getPositionInfo().getParentClass();
         int startLine = activeStatement.getStartPosition().getLine();
         int endLine = activeStatement.getEndPosition().getLine();
         boolean isInLine = endLine>startLine+1 ? shouldStopInLine(startLine, path) : shouldStopInLine(endLine, path);
         return isInLine;
      }
      return false;
   }
   
   /**
    * Returns the line number of the associated Breakpoint.
    * @return the line number of the associated Breakpoint
    */
   public int getLineNumber() {
      return lineNumber;
   }
   
   @Override
   protected boolean isInScope(Node node) {
      Node checkNode = node;
      while (checkNode != null) {
         SourceElement activeStatement = NodeInfo.computeActiveStatement(checkNode.getAppliedRuleApp());
         if (activeStatement != null && activeStatement.getStartPosition() != Position.UNDEFINED) {
            if (activeStatement.getStartPosition().getLine() >= methodStart && activeStatement.getEndPosition().getLine() <= methodEnd) {
               return true;
            }
            break;
         }
         checkNode = checkNode.parent();
      }
      return false;
   }
   
   @Override
   protected boolean isInScopeForCondition(Node node) {
      Node checkNode = node;
      while (checkNode != null) {
         SourceElement activeStatement = NodeInfo.computeActiveStatement(checkNode.getAppliedRuleApp());
         if (activeStatement != null && activeStatement.getStartPosition() != Position.UNDEFINED) {
            if (activeStatement.getStartPosition().getLine() >= methodStart && activeStatement.getEndPosition().getLine() <= methodEnd && activeStatement instanceof LocalVariableDeclaration) {
               return true;
            }
            break;
         }
         checkNode = checkNode.parent();
      }
      return false;
   }

   /**
    * @return the classPath
    */
   public String getClassPath() {
      return classPath;
   }

   /**
    * @param classPath the classPath to set
    */
   public void setClassPath(String classPath) {
      this.classPath = classPath;
   }
}