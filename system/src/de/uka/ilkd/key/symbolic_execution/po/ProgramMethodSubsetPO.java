package de.uka.ilkd.key.symbolic_execution.po;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
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
    */
   public ProgramMethodSubsetPO(InitConfig initConfig, 
                       String name, 
                       IProgramMethod pm, 
                       String precondition,
                       Position startPosition,
                       Position endPosition,
                       boolean addUninterpretedPredicate) {
      super(initConfig, name, pm, precondition, addUninterpretedPredicate);
      assert startPosition != null;
      assert endPosition != null;
      this.startPosition = startPosition;
      this.endPosition = endPosition;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected StatementBlock buildOperationBlock(ImmutableList<LocationVariable> formalParVars,
                                                ProgramVariable selfVar, 
                                                ProgramVariable resultVar) {
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
         register(x);
      }
      return result;
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
                               List<LocationVariable> heaps) {
      ImmutableList<ProgramVariable> paramVarsList = convert(undeclaredVariableCollector.result());
      return super.buildFreePre(selfVar, selfKJT, paramVarsList, heaps);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Term buildUninterpretedPredicate(ImmutableList<ProgramVariable> paramVars, 
                                              ProgramVariable exceptionVar,
                                              String name) {
      ImmutableList<ProgramVariable> paramVarsList = convert(undeclaredVariableCollector.result());
      return super.buildUninterpretedPredicate(paramVarsList, exceptionVar, name);
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
}
