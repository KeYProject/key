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
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.KeYJMLParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;

/**
 * <p>
 * This proof obligation executes selected statements of the body
 * of a given {@link IProgramMethod}. The statements are selected by its
 * source location. All statements in the given source range are executed.
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
public class MethodPartPO extends AbstractOperationPO {
   /**
    * The {@link IProgramMethod} to execute code parts from.
    */
   private IProgramMethod pm;
   
   /**
    * The precondition in JML syntax.
    */
   private String precondition;

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
   public MethodPartPO(InitConfig initConfig, 
                       String name, 
                       IProgramMethod pm, 
                       String precondition,
                       Position startPosition,
                       Position endPosition) {
      super(initConfig, name);
      assert pm != null;
      assert startPosition != null;
      assert endPosition != null;
      this.pm = pm;
      this.precondition = precondition;
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
   public MethodPartPO(InitConfig initConfig, 
                       String name, 
                       IProgramMethod pm, 
                       String precondition,
                       Position startPosition,
                       Position endPosition,
                       boolean addUninterpretedPredicate) {
      super(initConfig, name, addUninterpretedPredicate);
      assert pm != null;
      assert startPosition != null;
      assert endPosition != null;
      this.pm = pm;
      this.precondition = precondition;
      this.startPosition = startPosition;
      this.endPosition = endPosition;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IProgramMethod getProgramMethod() {
      return pm;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isTransactionApplicable() {
      return false;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected KeYJavaType getCalleeKeYJavaType() {
      return pm.getContainerType();
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
      for (int i = 0; i < container.getChildCount(); i++) {
         Statement s = container.getStatementAt(i);
         if (s.getStartPosition().compareTo(startPosition) >= 0 &&
             s.getEndPosition().compareTo(endPosition) <= 0) {
            // Statement found
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
   protected Term generateMbyAtPreDef(ProgramVariable selfVar,
                                      ImmutableList<ProgramVariable> paramVars) {
      return TB.tt();
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
      try {
         if (precondition != null && !precondition.isEmpty()) {
            PositionedString ps = new PositionedString(precondition);
            ImmutableList<ProgramVariable> paramVarsList = convert(undeclaredVariableCollector.result());
            KeYJMLParser parser = new KeYJMLParser(ps, 
                                                   services, 
                                                   getCalleeKeYJavaType(), 
                                                   selfVar, 
                                                   paramVarsList, 
                                                   null, 
                                                   null, 
                                                   null);
            return parser.parseExpression();
         }
         else {
            return TB.tt();
         }
      }
      catch (SLTranslationException e) {
         throw new RuntimeException("Can't parse precondition \"" + precondition + "\".", e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Term getPost(List<LocationVariable> modHeaps,
                          ProgramVariable selfVar, 
                          ImmutableList<ProgramVariable> paramVars, 
                          ProgramVariable resultVar, 
                          ProgramVariable exceptionVar, 
                          Map<LocationVariable, LocationVariable> atPreVars, 
                          Services services) {
      return TB.tt();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Term buildFrameClause(List<LocationVariable> modHeaps,
                                   Map<LocationVariable, Map<Term, Term>> heapToAtPre,
                                   ProgramVariable selfVar, 
                                   ImmutableList<ProgramVariable> paramVars) {
      return TB.tt();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Modality getTerminationMarker() {
      return Modality.DIA;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Term buildUpdate(ImmutableList<ProgramVariable> paramVars,
                              ImmutableList<LocationVariable> formalParamVars,
                              Map<LocationVariable, LocationVariable> atPreVars) {
      Term update = null;
      for(LocationVariable heap : atPreVars.keySet()) {
         final Term u = TB.elementary(services, atPreVars.get(heap), TB.getBaseHeap(services));
         if(update == null) {
            update = u;
         }else{
            update = TB.parallel(update, u);
         }
       }
       return update;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String buildPOName(boolean transactionFlag) {
      return name;
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
                                              String name) {
      ImmutableList<ProgramVariable> paramVarsList = convert(undeclaredVariableCollector.result());
      return super.buildUninterpretedPredicate(paramVarsList, name);
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
      return pm.hashCode() + 
             (precondition != null ? precondition.hashCode() : 0);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean equals(Object obj) {
      if (obj instanceof MethodPartPO) {
         MethodPartPO other = (MethodPartPO)obj;
         return JavaUtil.equals(pm, other.getProgramMethod()) &&
                JavaUtil.equals(precondition, other.getPrecondition());
      }
      else {
         return false;
      }
   }
   
   /**
    * Returns the precondition in JML syntax.
    * @return The precondition in JML syntax.
    */
   public String getPrecondition() {
      return precondition;
   }
}
