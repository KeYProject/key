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

package de.uka.ilkd.key.symbolic_execution.po;

import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.java.visitor.UndeclaredProgramVariableCollector;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;

/**
 * <p>
 * This proof obligation executes selected statements of the body
 * of a given {@link IProgramMethod}. The statements are selected by its
 * source location. All statements which ends in the given source range
 * ]{@code startPosition}, {@code endPosition}] are executed.
 * </p>
 * <p>
 * To select statements by its end position is required, because KeY's recorder
 * includes also leading space and leading comments into a statements position.
 * Another drawback is that the end position of the previous statement is
 * exactly the start position of the following statement.
 * </p>
 * <p>
 * Imagine the following snippet:
 * <code><pre>
 * int x = 1; // from 3/59 to 4/16
 * int y = 2; // from 4/16 to 5/16
 * int z = 3; // from 5/16 to 6/16
 * </pre></code>
 * To execute only the last two statements a user would select intuitively
 * the source range 5/0 to 6/16 (the text without leading white space) which
 * matches exactly the used selection definition.
 * </p>
 * <p>
 * The generated {@link Sequent} has the following form:
 * <pre>
 * <code>
 * ==>
 * &lt;generalAssumptions&gt; &
 * &lt;preconditions&gt;
 * ->
 * &lt;updatesToStoreInitialValues&gt;
 * &lt;modalityStart&gt;
 * exc=null;try {&lt;methodFrame&gt;&lt;selectedStatements&gt;}catch(java.lang.Exception e) {exc = e}
 * &lt;modalityEnd&gt;
 * (exc = null & &lt;postconditions &gt; & &lt;optionalUninterpretedPredicate&gt;)
 * </code>
 * </pre>
 * </p>
 * @author Martin Hentschel
 */
public class ProgramMethodSubsetPO extends ProgramMethodPO {
   /**
    * Contains all undeclared variables used in the method part to execute.
    */
   private UndeclaredProgramVariableCollector undeclaredVariableCollector;

   /**
    * The start position.
    */
   private Position startPosition;

   /**
    * The end position.
    */
   private Position endPosition;

   /**
    * Constructor.
    * @param initConfig The {@link InitConfig} to use.
    * @param name The name to use.
    * @param pm The {@link IProgramMethod} to execute code parts from.
    * @param precondition An optional precondition to use.
    * @param startPosition The start position.
    * @param endPosition The end position.
    */
   public ProgramMethodSubsetPO(InitConfig initConfig,
                                String name,
                                IProgramMethod pm,
                                String precondition,
                                Position startPosition,
                                Position endPosition) {
      super(initConfig, name, pm, precondition);
      assert startPosition != null;
      assert endPosition != null;
      this.startPosition = startPosition;
      this.endPosition = endPosition;
   }

   /**
    * Constructor.
    * @param initConfig The {@link InitConfig} to use.
    * @param name The name to use.
    * @param pm The {@link IProgramMethod} to execute code parts from.
    * @param precondition An optional precondition to use.
    * @param startPosition The start position.
    * @param endPosition The end position.
    * @param addUninterpretedPredicate {@code true} postcondition contains uninterpreted predicate, {@code false} uninterpreted predicate is not contained in postcondition.
    * @param addSymbolicExecutionLabel {@code true} to add the {@link SymbolicExecutionTermLabel} to the modality, {@code false} to not label the modality.
    */
   public ProgramMethodSubsetPO(InitConfig initConfig,
                                String name,
                                IProgramMethod pm,
                                String precondition,
                                Position startPosition,
                                Position endPosition,
                                boolean addUninterpretedPredicate,
                                boolean addSymbolicExecutionLabel) {
      super(initConfig, name, pm, precondition, addUninterpretedPredicate, addSymbolicExecutionLabel);
      assert startPosition != null;
      assert endPosition != null;
      this.startPosition = startPosition;
      this.endPosition = endPosition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ImmutableList<StatementBlock> buildOperationBlocks(ImmutableList<LocationVariable> formalParVars,
                                                ProgramVariable selfVar,
                                                ProgramVariable resultVar, Services services) {
      // Get program method to execute
      KeYJavaType type = getCalleeKeYJavaType();
      IProgramMethod pm = getProgramMethod();
      // Extracts code parts of the method
      List<Statement> statementsToExecute = new LinkedList<Statement>();
      collectStatementsToExecute(statementsToExecute, pm.getBody());
      Statement[] statements = statementsToExecute.toArray(new Statement[statementsToExecute.size()]);
      StatementBlock blockToExecute = new StatementBlock(statements);
      MethodFrame mf = new MethodFrame(endsWithReturn(statements) ? resultVar : null,
                                       new ExecutionContext(new TypeRef(type), pm, selfVar),
                                       blockToExecute);
      StatementBlock result = new StatementBlock(mf);
      // Collect undeclared variables
      undeclaredVariableCollector = new UndeclaredProgramVariableCollector(result, services);
      undeclaredVariableCollector.start();
      // Register undeclared variables
      Set<LocationVariable> undeclaredVariables = undeclaredVariableCollector.result();
      for (LocationVariable x : undeclaredVariables) {
         register(x, services);
      }
      return ImmutableSLList.<StatementBlock>nil().prepend(null, result, null, null);
   }

   /**
    * Collects recursive the {@link Statement}s which are in the given source range
    * defined by {@link #startPosition} and {@link #endPosition}.
    * @param toFill The result {@link List} to fill.
    * @param container The {@link StatementContainer} to seach in.
    */
   protected void collectStatementsToExecute(List<Statement> toFill, StatementContainer container) {
      for (int i = 0; i < container.getStatementCount(); i++) {
         Statement s = container.getStatementAt(i);
         if (s.getEndPosition().compareTo(startPosition) > 0 &&
             s.getEndPosition().compareTo(endPosition) <= 0) {
            // Statement found which ends in the interval ]startPosition, endPosition]
            toFill.add(s);
         }
         else {
            // Continue search in children
            if (s instanceof StatementContainer) {
               collectStatementsToExecute(toFill, (StatementContainer)s);
            }
            else if (s instanceof BranchStatement) {
               BranchStatement bs = (BranchStatement)s;
               for (int j = 0; j < bs.getBranchCount(); j++) {
                  Branch branch = bs.getBranchAt(j);
                  collectStatementsToExecute(toFill, branch);
               }
            }
         }
      }
   }

   /**
    * Checks if the last statement is a {@link Return} statement.
    * @param statements The statements to check.
    * @return {@code true} last statement is {@link Return}, {@code false} statements are empty or last statement is something else.
    */
   protected boolean endsWithReturn(Statement[] statements) {
      if (statements != null && statements.length >= 1) {
         return statements[statements.length - 1] instanceof Return;
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Term getPre(List<LocationVariable> modHeaps,
                         ProgramVariable selfVar,
                         ImmutableList<ProgramVariable> paramVars,
                         Map<LocationVariable, LocationVariable> atPreVars,
                         Services services) {
      ImmutableList<ProgramVariable> paramVarsList = convert(undeclaredVariableCollector.result());
      return super.getPre(modHeaps, selfVar, paramVarsList, atPreVars, services);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Term buildFreePre(ProgramVariable selfVar,
                               KeYJavaType selfKJT,
                               ImmutableList<ProgramVariable> paramVars,
                               List<LocationVariable> heaps,
                               Services proofServices) {
      ImmutableList<ProgramVariable> paramVarsList = convert(undeclaredVariableCollector.result());
      return super.buildFreePre(selfVar, selfKJT, paramVarsList, heaps, proofServices);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Term buildUninterpretedPredicate(ImmutableList<ProgramVariable> paramVars,
                                              ProgramVariable exceptionVar,
                                              String name,
                                              Services proofServices) {
      ImmutableList<ProgramVariable> paramVarsList = convert(undeclaredVariableCollector.result());
      return super.buildUninterpretedPredicate(paramVarsList, exceptionVar, name, proofServices);
   }

   /**
    * Converts the given {@link Collection} into an {@link ImmutableList}.
    * @param c The {@link Collection} to convert.
    * @return The created {@link ImmutableList}.
    */
   protected static ImmutableList<ProgramVariable> convert(Collection<LocationVariable> c) {
      ImmutableList<ProgramVariable> result = ImmutableSLList.nil();
      for (LocationVariable var : c) {
         result = result.append(var);
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int hashCode() {
      return super.hashCode() +
             (getStartPosition() != null ? getStartPosition().hashCode() : 0) +
             (getEndPosition() != null ? getEndPosition().hashCode() : 0);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean equals(Object obj) {
      if (obj instanceof ProgramMethodSubsetPO) {
         ProgramMethodSubsetPO other = (ProgramMethodSubsetPO)obj;
         return super.equals(obj) &&
                JavaUtil.equals(getStartPosition(), other.getStartPosition()) &&
                JavaUtil.equals(getEndPosition(), other.getEndPosition());
      }
      else {
         return false;
      }
   }

   /**
    * Returns the start position.
    * @return The start position.
    */
   public Position getStartPosition() {
      return startPosition;
   }

   /**
    * Returns the end position.
    * @return The end position.
    */
   public Position getEndPosition() {
      return endPosition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void fillSaveProperties(Properties properties) throws IOException {
       super.fillSaveProperties(properties);
       if (getStartPosition() != null) {
          properties.setProperty("startLine", getStartPosition().getLine() + "");
          properties.setProperty("startColumn", getStartPosition().getColumn() + "");
       }
       if (getEndPosition() != null) {
          properties.setProperty("endLine", getEndPosition().getLine() + "");
          properties.setProperty("endColumn", getEndPosition().getColumn() + "");
       }
   }

   /**
    * Instantiates a new proof obligation with the given settings.
    * @param initConfig The already load {@link InitConfig}.
    * @param properties The settings of the proof obligation to instantiate.
    * @return The instantiated proof obligation.
    * @throws IOException Occurred Exception.
    */
   public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws IOException {
      return new LoadedPOContainer(new ProgramMethodSubsetPO(initConfig,
                                                             getName(properties),
                                                             getProgramMethod(initConfig, properties),
                                                             getPrecondition(properties),
                                                             getStartPosition(properties),
                                                             getEndPosition(properties),
                                                             isAddUninterpretedPredicate(properties),
                                                             isAddSymbolicExecutionLabel(properties)));
   }

   /**
    * Extracts the start position from the given {@link Properties}.
    * @param properties The proof obligation settings to read from.
    * @return The defined start {@link Position}.
    * @throws IOException Occurred Exception if it was not possible to read the start position.
    */
   protected static Position getStartPosition(Properties properties) throws IOException{
      String line = properties.getProperty("startLine");
      if (line == null || line.isEmpty()) {
         throw new IOException("Start line property \"startLine\" is not available or empty.");
      }
      String column = properties.getProperty("startColumn");
      if (column == null || column.isEmpty()) {
         throw new IOException("Start column property \"startColumn\" is not available or empty.");
      }
      int lineValue;
      try {
         lineValue = Integer.parseInt(line);
      }
      catch (NumberFormatException e) {
         throw new IOException("Start line \"" + line + "\" is no valid integer.");
      }
      if (lineValue < 0) {
         throw new IOException("Start line \"" + line + "\" is a negative integer.");
      }
      int columnValue;
      try {
         columnValue = Integer.parseInt(column);
      }
      catch (NumberFormatException e) {
         throw new IOException("Start column \"" + column + "\" is no valid integer.");
      }
      if (columnValue < 0) {
         throw new IOException("Start column \"" + column + "\" is a negative integer.");
      }
      return new Position(lineValue, columnValue);
   }

   /**
    * Extracts the end position from the given {@link Properties}.
    * @param properties The proof obligation settings to read from.
    * @return The defined end {@link Position}.
    * @throws IOException Occurred Exception if it was not possible to read the end position.
    */
   protected static Position getEndPosition(Properties properties) throws IOException {
      String line = properties.getProperty("endLine");
      if (line == null || line.isEmpty()) {
         throw new IOException("End line property \"endLine\" is not available or empty.");
      }
      String column = properties.getProperty("endColumn");
      if (column == null || column.isEmpty()) {
         throw new IOException("End column property \"endColumn\" is not available or empty.");
      }
      int lineValue;
      try {
         lineValue = Integer.parseInt(line);
      }
      catch (NumberFormatException e) {
         throw new IOException("End line \"" + line + "\" is no valid integer.");
      }
      if (lineValue < 0) {
         throw new IOException("End line \"" + line + "\" is a negative integer.");
      }
      int columnValue;
      try {
         columnValue = Integer.parseInt(column);
      }
      catch (NumberFormatException e) {
         throw new IOException("End column \"" + column + "\" is no valid integer.");
      }
      if (columnValue < 0) {
         throw new IOException("End column \"" + column + "\" is a negative integer.");
      }
      return new Position(lineValue, columnValue);
   }
}