package org.key_project.sed.key.core.symbolic_execution.model.impl;

import org.eclipse.core.runtime.Assert;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionMethodCall;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionMethodReturn;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionNode;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.ProofStarter;

/**
 * The default implementation of {@link IExecutionMethodReturn}.
 * @author Martin Hentschel
 */
public class ExecutionMethodReturn extends AbstractExecutionStateNode<SourceElement> implements IExecutionMethodReturn {
   /**
    * The {@link IExecutionMethodCall} which is now returned.
    */
   private IExecutionMethodCall methodCall;
   
   /**
    * The node name including the return value.
    */
   private String nameIncludingReturnValue;
   
   /**
    * The return value.
    */
   private Term returnValue;
   
   /**
    * The return value formated for the user.
    */
   private String formatedReturnValue;
   
   /**
    * Constructor.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param methodCall The {@link IExecutionMethodCall} which is now returned.
    */
   public ExecutionMethodReturn(Node proofNode, IExecutionMethodCall methodCall) {
      super(proofNode);
      assert methodCall != null;
      this.methodCall = methodCall;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionMethodCall getMethodCall() {
      return methodCall;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return createMethodReturnName(null, getMethodCall().getName());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNameIncludingReturnValue() throws ProofInputException {
      if (nameIncludingReturnValue == null) {
         nameIncludingReturnValue = lazyComputeNameIncludingReturnValue();
      }
      return nameIncludingReturnValue;
   }

   /**
    * Computes the name including the return value lazily when
    * {@link #getNameIncludingReturnValue()} is called the first time.
    * @return The name including the return value.
    * @throws Occurred Exception.
    */
   protected String lazyComputeNameIncludingReturnValue() throws ProofInputException {
      return createMethodReturnName(getFormatedReturnValue(), getMethodCall().getName());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedReturnValue() throws ProofInputException {
      if (returnValue == null) {
         lazyComputeReturnValue();
      }
      return formatedReturnValue;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   // TODO: Return value can be unknown in SET, e.g. quotient in TryCatchFinally test
   public Term getReturnValue() throws ProofInputException {
      if (returnValue == null) {
         lazyComputeReturnValue();
      }
      return returnValue;
   }
   
   /**
    * Computes the return value lazily when
    * {@link #getReturnValue()} is called the first time.
    * @return The return value.
    * @throws ProofInputException Occurred Exception.
    */
   protected void lazyComputeReturnValue() throws ProofInputException {
      // Check if a result variable is available
      MethodBodyStatement mbs = getMethodCall().getActiveStatement();
      IProgramVariable resultVar = mbs.getResultVariable();
      if (resultVar != null) {
         // Search the node with applied rule "methodCallReturn" which provides the required updates
         Node methodReturnNode = findMethodReturnNode(getProofNode());
         if (methodReturnNode != null) {
            // Start site proof to extract the value of the result variable.
            SiteProofVariableValueInput sequentToProve = createExtractVariableValueSequent(mbs.getBodySourceAsTypeReference(),  
                                                                                           mbs.getDesignatedContext(), 
                                                                                           methodReturnNode, 
                                                                                           resultVar);
            ApplyStrategy.ApplyStrategyInfo info = startSiteProof(sequentToProve.getSequentToProve());
            returnValue = extractOperatorValue(info, sequentToProve.getOperator());
            // Format return vale
            StringBuffer sb = ProofSaver.printTerm(returnValue, info.getProof().getServices(), true);
            formatedReturnValue = sb.toString();
         }
      }
   }
   
   /**
    * Searches from the given {@link Node} the parent which applies
    * the rule "methodCallReturn".
    * @param node The {@link Node} to start search from.
    * @return The found {@link Node} with rule "methodCallReturn" or {@code null} if no node was found.
    */
   protected Node findMethodReturnNode(Node node) {
      Node resultNode = null;
      while (node != null && resultNode == null) {
         if ("methodCallReturn".equals(KeYUtil.getRuleDisplayName(node))) {
            resultNode = node;
         }
         node = node.parent();
      }
      return resultNode;
   }

   /**
    * Creates the human readable name which is shown in {@link IExecutionMethodReturn} instances.
    * @param returnValue The return value.
    * @param methodName The name of the method that is completely executed.
    * @return The created human readable name.
    */
   public static String createMethodReturnName(Object returnValue, String methodName) {
      return INTERNAL_NODE_NAME_START + "return" +
             (returnValue != null ? " '" + returnValue + "' as result" : StringUtil.EMPTY_STRING) +
             (!StringUtil.isTrimmedEmpty(methodName) ? " of " + methodName : StringUtil.EMPTY_STRING) +
             INTERNAL_NODE_NAME_END;
   }
   
   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param contextObjectType The type of the current object (this reference).
    * @param contextObject The current object (this reference).
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   protected SiteProofVariableValueInput createExtractVariableValueSequent(TypeReference contextObjectType,
                                                                           ReferencePrefix contextObject,
                                                                           Node node,
                                                                           IProgramVariable variable) {
      // Create execution context in that the method was called.
      IExecutionContext context = new ExecutionContext(contextObjectType, contextObject);
      // Create sequent
      return createExtractVariableValueSequent(context, node, variable);
   }

   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param context The {@link IExecutionContext} that defines the current object (this reference).
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   protected SiteProofVariableValueInput createExtractVariableValueSequent(IExecutionContext context,
                                                                           Node node,
                                                                           IProgramVariable variable) {
      // Make sure that correct parameters are given
      Assert.isNotNull(context);
      Assert.isNotNull(node);
      Assert.isTrue(variable instanceof ProgramVariable);
      // Create method frame which will be executed in site proof
      Statement originalReturnStatement = (Statement)node.getNodeInfo().getActiveStatement();
      MethodFrame newMethodFrame = new MethodFrame(variable, context, new StatementBlock(originalReturnStatement));
      JavaBlock newJavaBlock = JavaBlock.createJavaBlock(new StatementBlock(newMethodFrame));
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(TermBuilder.DF.newName(getServices(), "ResultPredicate")), Sort.FORMULA, variable.sort());
      // Create formula which contains the value interested in.
      Term newTerm = TermBuilder.DF.func(newPredicate, TermBuilder.DF.var((ProgramVariable)variable));
      // Combine method frame with value formula in a modality.
      Term modalityTerm = TermBuilder.DF.dia(newJavaBlock, newTerm);
      // Get the updates from the return node which includes the value interested in.
      Term originalModifiedFormula = node.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
      ImmutableList<Term> originalUpdates = MiscTools.goBelowUpdates2(originalModifiedFormula).first;
      // Combine method frame, formula with value predicate and the updates which provides the values
      Term newSuccedentToProve = TermBuilder.DF.applySequential(originalUpdates, modalityTerm);
      // Create new sequent with the original antecedent and the formulas in the succedent which were not modified by the applied rule
      PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
      Sequent originalSequentWithoutMethodFrame = node.sequent().removeFormula(pio).sequent();
      Sequent sequentToProve = originalSequentWithoutMethodFrame.addFormula(new SequentFormula(newSuccedentToProve), false, true).sequent();
      // Return created sequent and the used predicate to identify the value interested in.
      return new SiteProofVariableValueInput(sequentToProve, newPredicate);
   }
   
   /**
    * Helper class which represents the return value of
    * {@link ExecutionMethodReturn#createExtractVariableValueSequent(TypeReference, ReferencePrefix, Node, IProgramVariable)} and
    * {@link ExecutionMethodReturn#createExtractVariableValueSequent(IExecutionContext, Node, IProgramVariable)}.
    * @author Martin Hentschel
    */
   protected static class SiteProofVariableValueInput {
      /**
       * The sequent to prove.
       */
      private Sequent sequentToProve;
      
      /**
       * The {@link Operator} which is the predicate that contains the value interested in.
       */
      private Operator operator;
      
      /**
       * Constructor.
       * @param sequentToProve he sequent to prove.
       * @param operator The {@link Operator} which is the predicate that contains the value interested in.
       */
      public SiteProofVariableValueInput(Sequent sequentToProve, Operator operator) {
         super();
         this.sequentToProve = sequentToProve;
         this.operator = operator;
      }
      
      /**
       * Returns the sequent to prove.
       * @return The sequent to prove.
       */
      public Sequent getSequentToProve() {
         return sequentToProve;
      }
      
      /**
       * Returns the {@link Operator} which is the predicate that contains the value interested in.
       * @return The {@link Operator} which is the predicate that contains the value interested in.
       */
      public Operator getOperator() {
         return operator;
      }
   }
   
   /**
    * Starts a site proof for the given {@link Sequent}.
    * @param sequentToProve The {@link Sequent} to prove.
    * @return The proof result represented as {@link ApplyStrategyInfo} instance.
    * @throws ProofInputException Occurred Exception
    */
   protected ApplyStrategyInfo startSiteProof(Sequent sequentToProve) throws ProofInputException {
      // Make sure that valid parameters are given
      Assert.isNotNull(sequentToProve);
      // Create ProofStarter
      ProofStarter starter = new ProofStarter();
      // Configure ProofStarter
      starter.init(sequentToProve, getProof().env());
      starter.setMaxRuleApplications(1000);
      StrategyProperties sp = getProof().getSettings().getStrategySettings().getActiveStrategyProperties(); // Is a clone that can be modified
      sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_OFF); // Logical Splitting: Off
      sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_NONE); // Method Treatement: Off
      sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_OFF); // Dependency Contracts: Off
      sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_OFF); // Query Treatment: Off
      sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS); // Arithmetic Treatment: DefOps
      sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NONE); // Quantifier treatment: All except Free 
      starter.setStrategy(sp);
      // Execute proof in the current thread
      return starter.start();
   }
   
   /**
    * Extracts the value for the formula with the given {@link Operator}
    * from the site proof result ({@link ApplyStrategyInfo}).
    * @param info The site proof result.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The value of the formula with the given {@link Operator}.
    * @throws ProofInputException Occurred Exception.
    */
   protected Term extractOperatorValue(ApplyStrategyInfo info, final Operator operator) throws ProofInputException {
      // Make sure that valid parameters are given
      Assert.isNotNull(info);
      if (info.getProof().openGoals().size() != 1) {
         throw new ProofInputException("Assumption that return value extraction has one goal does not hold because " + info.getProof().openGoals().size() + " goals are available.");
      }
      // Get node of open goal
      Node goalNode = info.getProof().openGoals().head().node();
      // Search formula with the given operator in sequent
      SequentFormula sf = CollectionUtil.search(goalNode.sequent(), new IFilter<SequentFormula>() {
         @Override
         public boolean select(SequentFormula element) {
            return ObjectUtil.equals(element.formula().op(), operator);
         }
      });
      if (sf != null) {
         // Extract value
         return sf.formula().sub(0);
      }
      else {
         return null;
      }
   }
}
