package de.uka.ilkd.key.symbolic_execution.po;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
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
 * This proof obligation executes an {@link IProgramMethod} with
 * an optional precondition.
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
 * exc=null;try {&lt;methodBodyStatement&gt}catch(java.lang.Exception e) {exc = e}
 * &lt;modalityEnd&gt;
 * (exc = null & &lt;postconditions &gt; & &lt;optionalUninterpretedPredicate&gt;)
 * </code>
 * </pre>
 * </p>
 * @author Martin Hentschel
 */
public class ProgramMethodPO extends AbstractOperationPO {
   /**
    * The {@link IProgramMethod} to execute code parts from.
    */
   private IProgramMethod pm;
   
   /**
    * The precondition in JML syntax.
    */
   private String precondition;
   
   /**
    * Constructor.
    * @param initConfig The {@link InitConfig} to use.
    * @param name The name to use.
    * @param pm The {@link IProgramMethod} to execute code parts from.
    * @param precondition An optional precondition to use.
    */
   public ProgramMethodPO(InitConfig initConfig, 
                  String name, 
                  IProgramMethod pm, 
                  String precondition) {
      super(initConfig, name);
      assert pm != null;
      this.pm = pm;
      this.precondition = precondition;
   }
   
   /**
    * Constructor.
    * @param initConfig The {@link InitConfig} to use.
    * @param name The name to use.
    * @param pm The {@link IProgramMethod} to execute code parts from.
    * @param precondition An optional precondition to use.
    * @param addUninterpretedPredicate {@code true} postcondition contains uninterpreted predicate, {@code false} uninterpreted predicate is not contained in postcondition.
    */
   public ProgramMethodPO(InitConfig initConfig, 
                       String name, 
                       IProgramMethod pm, 
                       String precondition,
                       boolean addUninterpretedPredicate) {
      super(initConfig, name, addUninterpretedPredicate);
      assert pm != null;
      this.pm = pm;
      this.precondition = precondition;
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
      IProgramMethod pm = getProgramMethod();
      // Extracts code parts of the method
      ImmutableArray<Expression> args = new ImmutableArray<Expression>(formalParVars.toArray(new ProgramVariable[formalParVars.size()]));
      MethodBodyStatement mbs = new MethodBodyStatement(pm, selfVar, resultVar, args);
      StatementBlock result = new StatementBlock(mbs);
      return result;
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
            KeYJMLParser parser = new KeYJMLParser(ps, 
                                                   services, 
                                                   getCalleeKeYJavaType(), 
                                                   selfVar, 
                                                   paramVars, 
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
   protected boolean isMakeNamesUnique() {
      return false; // Unique names crashes precondition parsing if names are renamed.
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isCopyOfMethodArgumentsUsed() {
      return false;
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
   public int hashCode() {
      return pm.hashCode() + 
             (precondition != null ? precondition.hashCode() : 0);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean equals(Object obj) {
      if (obj instanceof ProgramMethodPO) {
         ProgramMethodPO other = (ProgramMethodPO)obj;
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
