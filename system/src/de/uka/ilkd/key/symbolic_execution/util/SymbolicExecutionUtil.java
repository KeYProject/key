package de.uka.ilkd.key.symbolic_execution.util;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionElement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionVariable;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.ProofStarter;

/**
 * Provides utility methods for symbolic execution with KeY.
 * @author Martin Hentschel
 */
public final class SymbolicExecutionUtil {
   /**
    * Key for the choice option "runtimeExceptions".
    */
   public static final String CHOICE_SETTING_RUNTIME_EXCEPTIONS = "runtimeExceptions";
  
   /**
    * Value in choice option "runtimeExceptions" to ban exceptions.
    */
   public static final String CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_BAN = "runtimeExceptions:ban";
   
   /**
    * Value in choice option "runtimeExceptions" to allow exceptions.
    */
   public static final String CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW = "runtimeExceptions:allow";

   /**
    * Forbid instances.
    */
   private SymbolicExecutionUtil() {
   }
   
   /**
    * Simplifies the given {@link Term} in a side proof. 
    * @param parentProof The parent {@link Proof}.
    * @param term The {@link Term} to simplify.
    * @return The simplified {@link Term}.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term simplify(Proof parentProof,
                               Term term) throws ProofInputException {
      // Create sequent to proof
      Sequent sequentToProve = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(term), false, true).sequent();
      // Return created sequent and the used predicate to identify the value interested in.
      ApplyStrategyInfo info = startSideProof(parentProof, sequentToProve);
      // The simplified formula is the conjunction of all open goals
      ImmutableList<Goal> openGoals = info.getProof().openEnabledGoals();
      ImmutableList<Term> goalImplications = ImmutableSLList.nil(); 
      for (Goal goal : openGoals) {
         Term goalImplication = sequentToImplication(goal.sequent());
         goalImplications = goalImplications.append(goalImplication);
      }
      return TermBuilder.DF.or(goalImplications);
   }
   
   /**
    * Converts the given {@link Sequent} into an implication.
    * @param sequent The {@link Sequent} to convert.
    * @return The created implication.
    */
   public static Term sequentToImplication(Sequent sequent) {
      if (sequent != null) {
         ImmutableList<Term> antecedents = listSemisequentTerms(sequent.antecedent());
         ImmutableList<Term> succedents = listSemisequentTerms(sequent.succedent());
         // Construct branch condition from created antecedent and succedent terms as new implication 
         Term left = TermBuilder.DF.and(antecedents);
         Term right = TermBuilder.DF.or(succedents);
         return TermBuilder.DF.imp(left, right);
      }
      else {
         return TermBuilder.DF.tt();
      }
   }
   
   /**
    * Lists the {@link Term}s contained in the given {@link Semisequent}.
    * @param semisequent The {@link Semisequent} to list terms of.
    * @return The list with all contained {@link Term}s.
    */
   public static ImmutableList<Term> listSemisequentTerms(Semisequent semisequent) {
      ImmutableList<Term> terms = ImmutableSLList.nil();
      if (semisequent != null) {
         for (SequentFormula sf : semisequent) {
            terms = terms.append(sf.formula());
         }
      }
      return terms;
   }
   
   /**
    * Creates a copy of the {@link ProofEnvironment} of the given {@link Proof}
    * which has his own {@link OneStepSimplifier} instance. Such copies are
    * required for instance during parallel usage of site proofs because
    * {@link OneStepSimplifier} has an internal state.
    * @param source The {@link Proof} to copy its {@link ProofEnvironment}.
    * @return The created {@link ProofEnvironment} which is a copy of the environment of the given {@link Proof} but with its own {@link OneStepSimplifier} instance.
    */
   public static ProofEnvironment cloneProofEnvironmentWithOwnOneStepSimplifier(Proof source) {
      assert source != null;
      // Get required source instances
      ProofEnvironment sourceEnv = source.env();
      InitConfig sourceInitConfig = sourceEnv.getInitConfig();
      RuleJustificationInfo sourceJustiInfo = sourceEnv.getJustifInfo();
      // Create new profile which has separate OneStepSimplifier instance
      JavaProfile profile = new JavaProfile() {
         private OneStepSimplifier simplifier;
         
         @Override
         protected OneStepSimplifier getInitialOneStepSimpilifier() {
            if (simplifier == null) {
               simplifier = new OneStepSimplifier();
            }
            return simplifier;
         }
      };
      // Create new InitConfig and initialize it with value from initial one.
      InitConfig initConfig = new InitConfig(source.getServices().copy(), profile);
      initConfig.setActivatedChoices(sourceInitConfig.getActivatedChoices());
      initConfig.setSettings(sourceInitConfig.getSettings());
      initConfig.setTaclet2Builder(sourceInitConfig.getTaclet2Builder());
      initConfig.setTaclets(sourceInitConfig.getTaclets());
      // Create new ProofEnvironment and initialize it with values from initial one.
      ProofEnvironment env = new ProofEnvironment(initConfig);
      env.setJavaModel(sourceEnv.getJavaModel());
      env.setNumber(sourceEnv.getNumber());
      env.setRuleConfig(sourceEnv.getRuleConfig());
      for (Taclet taclet : sourceInitConfig.activatedTaclets()) {
         env.getJustifInfo().addJustification(taclet, sourceJustiInfo.getJustification(taclet));
      }
      for (BuiltInRule rule : initConfig.builtInRules()) {
         RuleJustification origJusti = sourceJustiInfo.getJustification(rule);
         if (origJusti == null) {
            assert rule instanceof OneStepSimplifier;
            origJusti = AxiomJustification.INSTANCE;
         }
         env.getJustifInfo().addJustification(rule, origJusti);
      }
      return env;
   }
   
   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param services The {@link Services} to use.
    * @param contextObjectType The type of the current object (this reference).
    * @param contextMethod The current method.
    * @param contextObject The current object (this reference).
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   public static SiteProofVariableValueInput createExtractReturnVariableValueSequent(Services services,
                                                                                     TypeReference contextObjectType,
                                                                                     IProgramMethod contextMethod,
                                                                                     ReferencePrefix contextObject,
                                                                                     Node node,
                                                                                     IProgramVariable variable) {
      // Create execution context in that the method was called.
      IExecutionContext context = new ExecutionContext(contextObjectType, contextMethod, contextObject);
      // Create sequent
      return createExtractReturnVariableValueSequent(services, context, node, variable);
   }

   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param services The {@link Services} to use.
    * @param context The {@link IExecutionContext} that defines the current object (this reference).
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   public static SiteProofVariableValueInput createExtractReturnVariableValueSequent(Services services,
                                                                                     IExecutionContext context,
                                                                                     Node node,
                                                                                     IProgramVariable variable) {
      // Make sure that correct parameters are given
      assert context != null;
      assert node != null;
      assert variable instanceof ProgramVariable;
      // Create method frame which will be executed in site proof
      Statement originalReturnStatement = (Statement)node.getNodeInfo().getActiveStatement();
      MethodFrame newMethodFrame = new MethodFrame(variable, context, new StatementBlock(originalReturnStatement));
      JavaBlock newJavaBlock = JavaBlock.createJavaBlock(new StatementBlock(newMethodFrame));
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(TermBuilder.DF.newName(services, "ResultPredicate")), Sort.FORMULA, variable.sort());
      // Create formula which contains the value interested in.
      Term newTerm = TermBuilder.DF.func(newPredicate, TermBuilder.DF.var((ProgramVariable)variable));
      // Combine method frame with value formula in a modality.
      Term modalityTerm = TermBuilder.DF.dia(newJavaBlock, newTerm);
      // Get the updates from the return node which includes the value interested in.
      Term originalModifiedFormula = node.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
      ImmutableList<Term> originalUpdates = TermBuilder.DF.goBelowUpdates2(originalModifiedFormula).first;
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
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param services The {@link Services} to use.
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   public static SiteProofVariableValueInput createExtractVariableValueSequent(Services services,
                                                                               Node node,
                                                                               IProgramVariable variable) {
      // Make sure that correct parameters are given
      assert node != null;
      assert variable instanceof ProgramVariable;
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(TermBuilder.DF.newName(services, "ResultPredicate")), Sort.FORMULA, variable.sort());
      // Create formula which contains the value interested in.
      Term newTerm = TermBuilder.DF.func(newPredicate, TermBuilder.DF.var((ProgramVariable)variable));
      // Combine method frame with value formula in a modality.
      // Get the updates from the return node which includes the value interested in.
      Term originalModifiedFormula = node.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
      ImmutableList<Term> originalUpdates = TermBuilder.DF.goBelowUpdates2(originalModifiedFormula).first;
      // Combine method frame, formula with value predicate and the updates which provides the values
      Term newSuccedentToProve = TermBuilder.DF.applySequential(originalUpdates, newTerm);
      // Create new sequent with the original antecedent and the formulas in the succedent which were not modified by the applied rule
      PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
      Sequent originalSequentWithoutMethodFrame = node.sequent().removeFormula(pio).sequent();
      Sequent sequentToProve = originalSequentWithoutMethodFrame.addFormula(new SequentFormula(newSuccedentToProve), false, true).sequent();
      // Return created sequent and the used predicate to identify the value interested in.
      return new SiteProofVariableValueInput(sequentToProve, newPredicate);
   }

   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param services The {@link Services} to use.
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   public static SiteProofVariableValueInput createExtractTermSequent(Services services,
                                                                      Node node,
                                                                      Term term) {
      // Make sure that correct parameters are given
      assert node != null;
      assert term != null;
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(TermBuilder.DF.newName(services, "ResultPredicate")), Sort.FORMULA, term.sort());
      // Create formula which contains the value interested in.
      Term newTerm = TermBuilder.DF.func(newPredicate, term);
      // Get the updates from the return node which includes the value interested in.
      Term originalModifiedFormula = node.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
      ImmutableList<Term> originalUpdates = TermBuilder.DF.goBelowUpdates2(originalModifiedFormula).first;
      // Combine method frame, formula with value predicate and the updates which provides the values
      Term newSuccedentToProve = TermBuilder.DF.applySequential(originalUpdates, newTerm);
      // Create new sequent with the original antecedent and the formulas in the succedent which were not modified by the applied rule
      PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
      Sequent originalSequentWithoutMethodFrame = node.sequent().removeFormula(pio).sequent();
      Sequent sequentToProve = originalSequentWithoutMethodFrame.addFormula(new SequentFormula(newSuccedentToProve), false, true).sequent();
      // Return created sequent and the used predicate to identify the value interested in.
      return new SiteProofVariableValueInput(sequentToProve, newPredicate);
   }
   
   /**
    * Helper class which represents the return value of
    * {@link ExecutionMethodReturn#createExtractReturnVariableValueSequent(TypeReference, ReferencePrefix, Node, IProgramVariable)} and
    * {@link ExecutionMethodReturn#createExtractVariableValueSequent(IExecutionContext, Node, IProgramVariable)}.
    * @author Martin Hentschel
    */
   public static class SiteProofVariableValueInput {
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
    * @param proof The parent {@link Proof} of the site proof to do.
    * @param sequentToProve The {@link Sequent} to prove.
    * @return The proof result represented as {@link ApplyStrategyInfo} instance.
    * @throws ProofInputException Occurred Exception
    */
   public static ApplyStrategyInfo startSideProof(Proof proof,
                                                  Sequent sequentToProve) throws ProofInputException {
      // Make sure that valid parameters are given
      assert sequentToProve != null;
      // Create ProofStarter
      ProofStarter starter = new ProofStarter();
      // Configure ProofStarter
      ProofEnvironment env = SymbolicExecutionUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(proof); // New OneStepSimplifier is required because it has an internal state and the default instance can't be used parallel.
      starter.init(sequentToProve, env);
      starter.setMaxRuleApplications(1000);
      StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties(); // Is a clone that can be modified
      sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_OFF); // Logical Splitting: Off is faster and avoids splits, but Normal allows to determine that two objects are different.
      sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_NONE); // Method Treatment: Off
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
   public static Term extractOperatorValue(ApplyStrategyInfo info, final Operator operator) throws ProofInputException {
      // Make sure that valid parameters are given
      assert info != null;
      if (info.getProof().openGoals().size() != 1) {
         throw new ProofInputException("Assumption that return value extraction has one goal does not hold because " + info.getProof().openGoals().size() + " goals are available.");
      }
      // Get node of open goal
      Node goalNode = info.getProof().openGoals().head().node();
      // Search formula with the given operator in sequent
      SequentFormula sf = JavaUtil.search(goalNode.sequent(), new IFilter<SequentFormula>() {
         @Override
         public boolean select(SequentFormula element) {
            return JavaUtil.equals(element.formula().op(), operator);
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
   
   /**
    * Checks if the given {@link Term} represents a heap update,
    * in particular a store or create operation on a heap.
    * @param services The {@link Services} to use.
    * @param term The {@link Term} to check.
    * @return {@code true} is heap update, {@code false} is something else.
    */
   public static boolean isHeapUpdate(Services services, Term term) {
      boolean heapUpdate = false;
      if (term != null) {
         ImmutableArray<Term> subs = term.subs();
         if (subs.size() == 1) {
            Term sub = subs.get(0);
            if (sub.op() == services.getTypeConverter().getHeapLDT().getStore() ||
                sub.op() == services.getTypeConverter().getHeapLDT().getCreate()) {
               heapUpdate = true;
            }
         }
      }
      return heapUpdate;
   }
   
   /**
    * Creates for the given {@link IExecutionStateNode} the contained
    * root {@link IExecutionVariable}s.
    * @param node The {@link IExecutionStateNode} to create variables for.
    * @return The created {@link IExecutionVariable}s.
    */
   public static IExecutionVariable[] createExecutionVariables(IExecutionStateNode<?> node) {
      if (node != null) {
         Node proofNode = node.getProofNode();
         List<IProgramVariable> variables = new LinkedList<IProgramVariable>();
         // Add self variable
         IProgramVariable selfVar = findSelfTerm(proofNode);
         if (selfVar != null) {
            variables.add(selfVar);
         }
         // Add method parameters
         Node callNode = findMethodCallNode(node.getProofNode());
         if (callNode != null && callNode.getNodeInfo().getActiveStatement() instanceof MethodBodyStatement) {
            MethodBodyStatement mbs = (MethodBodyStatement)callNode.getNodeInfo().getActiveStatement();
            for (Expression e : mbs.getArguments()) {
               if (e instanceof IProgramVariable) {
                  variables.add((IProgramVariable)e);
               }
            }
         }
         // Collect variables from updates
         List<IProgramVariable> variablesFromUpdates = collectAllElementaryUpdateTerms(proofNode);
         for (IProgramVariable variable : variablesFromUpdates) {
            if (!variables.contains(variable)) {
               variables.add(variable);
            }
         }
         IExecutionVariable[] result = new IExecutionVariable[variables.size()];
         int i = 0;
         for (IProgramVariable var : variables) {
            result[i] = new ExecutionVariable(node.getMediator(), proofNode, var);
            i++;
         }
         return result;
      }
      else {
         return new IExecutionVariable[0];
      }
   }
   
   /**
    * Collects all {@link IProgramVariable} used in {@link ElementaryUpdate}s.
    * @param node The {@link Node} to search in.
    * @return The found {@link IProgramVariable} which are used in {@link ElementaryUpdate}s.
    */
   public static List<IProgramVariable> collectAllElementaryUpdateTerms(Node node) {
      if (node != null) {
         Services services = node.proof().getServices();
         List<IProgramVariable> result = new LinkedList<IProgramVariable>();
         for (SequentFormula sf : node.sequent().antecedent()) {
            internalCollectAllElementaryUpdateTerms(services, result, sf.formula());
         }
         for (SequentFormula sf : node.sequent().succedent()) {
            internalCollectAllElementaryUpdateTerms(services, result, sf.formula());
         }
         return result;
      }
      else {
         return Collections.emptyList();
      }
   }
   
   /**
    * Utility method of {@link #collectAllElementaryUpdateTerms(Node)} which
    * collects all {@link IProgramVariable}s of {@link ElementaryUpdate}s
    * and static field manipulations.
    * @param services The {@link Services} to use.
    * @param result The result {@link List} to fill.
    * @param term The current term to analyze.
    */
   private static void internalCollectAllElementaryUpdateTerms(Services services, List<IProgramVariable> result, Term term) {
      if (term != null) {
         if (term.op() instanceof ElementaryUpdate) {
            if (SymbolicExecutionUtil.isHeapUpdate(services, term)) {
               // Extract static variables from heap
               Set<IProgramVariable> staticAttributes = new LinkedHashSet<IProgramVariable>();
               internalCollectStaticProgramVariablesOnHeap(services, staticAttributes, term);
               result.addAll(staticAttributes);
            }
            else {
               // Local variable
               ElementaryUpdate eu = (ElementaryUpdate)term.op();
               if (eu.lhs() instanceof IProgramVariable) {
                  result.add((IProgramVariable)eu.lhs());
               }
            }
         }
         else {
            for (Term sub : term.subs()) {
               internalCollectAllElementaryUpdateTerms(services, result, sub);
            }
         }
      }
   }
   
   /**
    * Utility method of {@link #internalCollectAllElementaryUpdateTerms(Services, List, Term)}
    * which collects static field manipulations on the given heap update.
    * @param services The {@link Services} to use.
    * @param result The result {@link List} to fill.
    * @param term The current term to analyze.
    */
   private static void internalCollectStaticProgramVariablesOnHeap(Services services, Set<IProgramVariable> result, Term term) {
      final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
      try {
         if (term.op() == heapLDT.getStore()) {
            ImmutableArray<Term> subs = term.subs();
            if (subs.size() == 4) {
               Term locationTerm = subs.get(2);
               if (locationTerm.op() instanceof Function) {
                  Function function = (Function)locationTerm.op();
                  String typeName = heapLDT.getClassName(function);
                  KeYJavaType type = services.getJavaInfo().getKeYJavaType(typeName);
                  if (type != null) {
                     String fieldName = heapLDT.getPrettyFieldName(function);
                     ProgramVariable attribute = services.getJavaInfo().getAttribute(fieldName, type);
                     if (attribute != null && attribute.isStatic()) {
                        result.add(attribute);
                     }
                  }
               }
            }
         }
      }
      catch (Exception e) {
         // Can go wrong, nothing to do
      }
      for (Term sub : term.subs()) {
         internalCollectStaticProgramVariablesOnHeap(services, result, sub);
      }
   }

   /**
    * Searches the {@link IProgramVariable} of the current {@code this}/{@code self} reference.
    * @param node The {@link Node} to search in.
    * @return The found {@link IProgramVariable} with the current {@code this}/{@code self} reference or {@code null} if no one is available.
    */
   public static IProgramVariable findSelfTerm(Node node) {
      JavaBlock jb = node.getAppliedRuleApp().posInOccurrence().subTerm().javaBlock();
      Services services = node.proof().getServices();
      IExecutionContext context = JavaTools.getInnermostExecutionContext(jb, services);
      if (context instanceof ExecutionContext) {
         ReferencePrefix prefix = ((ExecutionContext)context).getRuntimeInstance();
         return prefix instanceof IProgramVariable ? (IProgramVariable)prefix : null;
      }
      else {
         return null;
      }
   }
   
//   /**
//    * Checks if the given {@link Node} contains an applied rule.
//    * @param node The {@link Node} to check.
//    * @return {@code true} node has applied rule, {@code false} node has no rule or node is {@code null}.
//    */
//   public static boolean hasAppliedRule(Node node) {
//      return node != null && node.getAppliedRuleApp() != null;
//   }
   
   /**
    * Checks if the given node should be represented as method call.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @param statement The statement ({@link SourceElement}).
    * @return {@code true} represent node as method call, {@code false} represent node as something else. 
    */
   public static boolean isMethodCallNode(Node node, RuleApp ruleApp, SourceElement statement) {
      return isMethodCallNode(node, ruleApp, statement, false);
   }
   
   /**
    * Checks if the given node should be represented as method call.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @param statement The statement ({@link SourceElement}).
    * @param allowImpliciteMethods {@code true} implicit methods are included, {@code false} implicit methods are outfiltered.
    * @return {@code true} represent node as method call, {@code false} represent node as something else. 
    */
   public static boolean isMethodCallNode(Node node, RuleApp ruleApp, SourceElement statement, boolean allowImpliciteMethods) {
      if (ruleApp != null) { // Do not handle open goal nodes without applied rule
         if (statement instanceof MethodBodyStatement) {
            if (allowImpliciteMethods) {
               return true;
            }
            else {
               MethodBodyStatement mbs = (MethodBodyStatement)statement;
               IProgramMethod pm = mbs.getProgramMethod(node.proof().getServices());
               return !pm.isImplicit(); // Do not include implicit methods
            }
         }
         else {
            return false;
         }
      }
      else {
         return false;
      }
   }
   
   /**
    * Checks if the given node should be represented as branch node.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @param statement The statement ({@link SourceElement}).
    * @param posInfo The {@link PositionInfo}.
    * @return {@code true} represent node as branch node, {@code false} represent node as something else. 
    */
   public static boolean isBranchNode(Node node, RuleApp ruleApp, SourceElement statement, PositionInfo posInfo) {
      return isStatementNode(node, ruleApp, statement, posInfo) &&
             (statement instanceof BranchStatement); 
   }
   
   /**
    * Checks if the given node should be represented as loop node.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @param statement The statement ({@link SourceElement}).
    * @param posInfo The {@link PositionInfo}.
    * @return {@code true} represent node as loop node, {@code false} represent node as something else. 
    */
   public static boolean isLoopNode(Node node, RuleApp ruleApp, SourceElement statement, PositionInfo posInfo) {
      return isStatementNode(node, ruleApp, statement, posInfo) &&
             (statement instanceof LoopStatement);
   }

   /**
    * <p>
    * Checks if the given {@link SourceElement} which represents a {@link LoopStatement} is executed
    * the first time in proof node or if it is a higher loop iteration.
    * </p>
    * <p>
    * The reason why such checks are required is that KeY's tacklet sometimes create
    * a copy in further loop iteration without a source code position and sometimes
    * is the original loop reused. The expected behavior of KeY should be to
    * reuse the original loop all the time to save memory. But the symbolic
    * execution tree should contain the loop statement only when it is executed
    * the first time and in further iterations only the checked loop condition.
    * For this reason is this check required.
    * </p>
    * <p>
    * <b>Attention:</b> This check requires to iterate over parent {@link Node}s
    * and can not be decided locally in the current {@link Node}.
    * This is a performance deficit.
    * </p>
    * @param node The current {@link Node} of the proof tree.
    * @param ruleApp The applied rule in {@link Node}.
    * @param statement The active {@link LoopStatement} of {@link Node} to check.
    * @return {@code true} it is the first loop iteration, {@code false} it is a second or higher loop iteration.
    */
   public static boolean isFirstLoopIteration(Node node, RuleApp ruleApp, SourceElement statement) {
      // Compute stack size of current node
      int stackSize = computeStackSize(node, ruleApp);
      // Iterate over all parents until another loop iteration is found or the current method was called
      boolean firstLoop = true;
      Node parent = node.parent();
      while (firstLoop && parent != null) {
         // Check if the current parent node treats the same loop
         SourceElement activeStatement = parent.getNodeInfo().getActiveStatement();
         firstLoop = activeStatement != statement;
         // Define parent for next iteration
         parent = parent.parent();
         // Check if the next parent is the method call of the current method, in this case iteration can stop
         if (isMethodCallNode(parent, parent.getAppliedRuleApp(), parent.getNodeInfo().getActiveStatement(), true) &&
             computeStackSize(parent, parent.getAppliedRuleApp()) < stackSize) {
            // Stop iteration because further parents are before the current method is called
            parent = null;
         }
      }
      return firstLoop;
   }

   /**
    * Checks if the given node should be represented as statement.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @param statement The statement ({@link SourceElement}).
    * @param posInfo The {@link PositionInfo}.
    * @return {@code true} represent node as statement, {@code false} represent node as something else. 
    */
   public static boolean isStatementNode(Node node, RuleApp ruleApp, SourceElement statement, PositionInfo posInfo) {
      return ruleApp != null && // Do not handle the open goal node which has no applied rule
             posInfo != null && 
             posInfo.getEndPosition() != Position.UNDEFINED &&
             posInfo.getEndPosition().getLine() >= 0;  // Filter out statements where source code is missing.
   }
   
   /**
    * Checks if the given node should be represented as termination.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} represent node as termination, {@code false} represent node as something else. 
    */
   public static boolean isTerminationNode(Node node, RuleApp ruleApp) {
      return "emptyModality".equals(MiscTools.getRuleDisplayName(ruleApp));
   }
   
   /**
    * Checks if the given node should be represented as method return.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} represent node as method return, {@code false} represent node as something else. 
    */
   public static boolean isMethodReturnNode(Node node, RuleApp ruleApp) {
      return "methodCallEmpty".equals(MiscTools.getRuleDisplayName(ruleApp));
   }

   /**
    * Checks if the given {@link Node} has a loop condition.
    * @param node The {@link Node} to check.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @param statement The actual statement ({@link SourceElement}).
    * @return {@code true} has loop condition, {@code false} has no loop condition.
    */
   public static boolean hasLoopCondition(Node node, RuleApp ruleApp, SourceElement statement) {
      return ruleApp != null && // Do not handle open goal nodes without applied rule
             statement instanceof LoopStatement && 
             !(statement instanceof EnhancedFor); // For each loops have no loop condition
   }
   
   /**
    * Checks if the given {@link Node} in KeY's proof tree represents
    * also a {@link Node} in a symbolic execution tree.
    * @param node The {@link Node} of KeY's proof tree to check.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} is also symbolic execution tree node, {@code false} is no node in a symbolic execution tree.
    */
   public static boolean isSymbolicExecutionTreeNode(Node node, RuleApp ruleApp) {
      if (node != null) {
         SourceElement statement = NodeInfo.computeActiveStatement(ruleApp);
         PositionInfo posInfo = statement != null ? statement.getPositionInfo() : null;
         if (isMethodReturnNode(node, ruleApp)) {
            return !isInImplicitMethod(node, ruleApp);
         }
         else if (isLoopNode(node, ruleApp, statement, posInfo)) { 
            return isFirstLoopIteration(node, ruleApp, statement);
         }
         else if (isBranchNode(node, ruleApp, statement, posInfo) ||
                  isMethodCallNode(node, ruleApp, statement) ||
                  isStatementNode(node, ruleApp, statement, posInfo) ||
                  isTerminationNode(node, ruleApp)) {
            return true;
         }
         else if (hasLoopCondition(node, ruleApp, statement)) {
            return ((LoopStatement)statement).getGuardExpression().getPositionInfo() != PositionInfo.UNDEFINED &&
                   !isDoWhileLoopCondition(node, statement) && 
                   !isForLoopCondition(node, statement);
         }
         else {
            return false;
         }
      }
      else {
         return false;
      }
   }
   
   /**
    * Checks if the currently executed code is in an implicit method
    * ({@link IProgramMethod#isImplicit()} is {@code true}).
    * @param node The {@link Node} of KeY's proof tree to check.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} is in implicit method, {@code false} is not in implicit method.
    */
   public static boolean isInImplicitMethod(Node node, RuleApp ruleApp) {
      Term term = ruleApp.posInOccurrence().constrainedFormula().formula();
      term = TermBuilder.DF.goBelowUpdates(term);
      JavaBlock block = term.javaBlock();
      IExecutionContext context = JavaTools.getInnermostExecutionContext(block, node.proof().getServices());
      return context != null && context.getMethodContext() != null && context.getMethodContext().isImplicit();
   }
   
   /**
    * Compute the stack size of the given {@link Node} in the proof tree of KeY.
    * @param node The {@link Node} to compute stack size for.
    * @param ruleApp The {@link RuleApp} which is or should be applied in the {@link Node}.
    * @return The stack size.
    */
   public static int computeStackSize(Node node, RuleApp ruleApp) {
      int result = 0;
      if (node != null && ruleApp != null) {
         PosInOccurrence posInOc = ruleApp.posInOccurrence();
         if (posInOc != null && posInOc.constrainedFormula() != null) {
            Term term = posInOc.constrainedFormula().formula();
            if (term != null && term.subs().size() == 2) {
               Term sub = term.sub(1);
               if (sub != null) {
                  JavaBlock block = sub.javaBlock();
                  if (block != null) {
                     JavaProgramElement element = block.program();
                     if (element instanceof StatementBlock) {
                        StatementBlock b = (StatementBlock)block.program();
                        ImmutableArray<ProgramPrefix> prefix = b.getPrefixElements();
                        result = JavaUtil.count(prefix, new IFilter<ProgramPrefix>() {
                           @Override
                           public boolean select(ProgramPrefix element) {
                              return element instanceof MethodFrame;
                           }
                        });
                     }
                  }
               }
            }
         }
      }
      return result;
   }
   
   /**
    * Checks if the given {@link SourceElement} is a do while loop.
    * @param node The {@link Node} to check.
    * @param statement The actual statement ({@link SourceElement}).
    * @return {@code true} is do while loop, {@code false} is something else.
    */
   public static boolean isDoWhileLoopCondition(Node node, SourceElement statement) {
      return statement instanceof Do;
   }
   
   /**
    * Checks if the given {@link SourceElement} is a for loop.
    * @param node The {@link Node} to check.
    * @param statement The actual statement ({@link SourceElement}).
    * @return {@code true} is for loop, {@code false} is something else.
    */
   public static boolean isForLoopCondition(Node node, SourceElement statement) {
      return statement instanceof For;
   }

   /**
    * Collects all {@link Goal}s in the subtree of the given {@link IExecutionElement}.
    * @param executionElement The {@link IExecutionElement} to collect {@link Goal}s in.
    * @return The found {@link Goal}s.
    */
   public static ImmutableList<Goal> collectGoalsInSubtree(IExecutionElement executionElement) {
      if (executionElement != null) {
         return collectGoalsInSubtree(executionElement.getProofNode());
      }
      else {
         return ImmutableSLList.nil();
      }
   }

   /**
    * Collects all {@link Goal}s in the subtree of the given {@link Node}.
    * @param node The {@link Node} to collect {@link Goal}s in.
    * @return The found {@link Goal}s.
    */
   public static ImmutableList<Goal> collectGoalsInSubtree(Node node) {
      ImmutableList<Goal> result = ImmutableSLList.nil();
      if (node != null) {
         Proof proof = node.proof();
         NodeIterator iter = node.leavesIterator();
         while (iter.hasNext()) {
            Node next = iter.next();
            Goal nextGoal = proof.getGoal(next);
            if (nextGoal != null) {
               result = result.append(nextGoal);
            }
         }
      }
      return result;
   }

   /**
    * Searches for the given {@link Node} the parent node
    * which also represents a symbolic execution tree node
    * (checked via {@link #isSymbolicExecutionTreeNode(Node, RuleApp)}).
    * @param node The {@link Node} to start search in.
    * @return The parent {@link Node} of the given {@link Node} which is also a set node or {@code null} if no parent node was found.
    */
   public static Node findMethodCallNode(Node node) {
      if (node != null && node.getAppliedRuleApp() != null) {
         // Get current program method
         Term term = node.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
         term = TermBuilder.DF.goBelowUpdates(term);
         Services services = node.proof().getServices();
         MethodFrame mf = JavaTools.getInnermostMethodFrame(term.javaBlock(), services);
         if (mf != null) {
            // Find call node
            Node parent = node.parent();
            Node result = null;
            while (parent != null && result == null) {
               SourceElement activeStatement = parent.getNodeInfo().getActiveStatement();
               if (activeStatement instanceof MethodBodyStatement && 
                   ((MethodBodyStatement)activeStatement).getProgramMethod(services) == mf.getProgramMethod()) {
                  result = parent;
               }
               else {
                  parent = parent.parent();
               }
            }
            return result;
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }

   /**
    * Searches for the given {@link Node} the parent node
    * which also represents a symbolic execution tree node
    * (checked via {@link #isSymbolicExecutionTreeNode(Node, RuleApp)}).
    * @param node The {@link Node} to start search in.
    * @return The parent {@link Node} of the given {@link Node} which is also a set node or {@code null} if no parent node was found.
    */
   public static Node findParentSetNode(Node node) {
      if (node != null) {
         Node parent = node.parent();
         Node result = null;
         while (parent != null && result == null) {
            if (isSymbolicExecutionTreeNode(parent, parent.getAppliedRuleApp())) {
               result = parent;
            }
            else {
               parent = parent.parent();
            }
         }
         return result;
      }
      else {
         return null;
      }
   }
   
   /**
    * Computes the branch condition of the given {@link Node}.
    * @param node The {@link Node} to compute its branch condition.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term computeBranchCondition(Node node) throws ProofInputException {
      // Get applied taclet on parent proof node
      Node parent = node.parent();
      assert parent.getAppliedRuleApp() instanceof TacletApp; // Splits of built in rules are currently not supported.
      TacletApp app = (TacletApp)parent.getAppliedRuleApp();
      // Find goal template which has created the represented proof node
      int childIndex = JavaUtil.indexOf(parent.childrenIterator(), node);
      TacletGoalTemplate goalTemplate = app.taclet().goalTemplates().take(childIndex).head();
      // Apply instantiations of schema variables to sequent of goal template
      Services services = node.proof().getServices();
      SVInstantiations instantiations = app.instantiations();
      ImmutableList<Term> antecedents = listSemisequentTerms(services, instantiations, goalTemplate.sequent().antecedent());
      ImmutableList<Term> succedents = listSemisequentTerms(services, instantiations, goalTemplate.sequent().succedent());
      // Construct branch condition from created antecedent and succedent terms as new implication 
      Term left = TermBuilder.DF.and(antecedents);
      Term right = TermBuilder.DF.or(succedents);
      Term implication = TermBuilder.DF.imp(left, right);
      Term result;
      // Check if an update context is available
      if (!instantiations.getUpdateContext().isEmpty()) {
         // Append update context because otherwise the formula is evaluated in wrong state
         result = TermBuilder.DF.applySequential(instantiations.getUpdateContext(), implication);
         // Simplify branch condition
         result = SymbolicExecutionUtil.simplify(node.proof(), result);
      }
      else {
         // No update context, just use the implication as branch condition
         result = implication;
      }
      return result;
   }

   /**
    * Applies the schema variable instantiations on the given {@link Semisequent}.
    * @param services The {@link Services} to use.
    * @param svInst The schema variable instantiations.
    * @param semisequent The {@link Semisequent} to apply instantiations on.
    * @return The list of created {@link Term}s in which schema variables are replaced with the instantiation.
    */
   private static ImmutableList<Term> listSemisequentTerms(Services services, 
                                                           SVInstantiations svInst, 
                                                           Semisequent semisequent) {
      ImmutableList<Term> terms = ImmutableSLList.nil();
      for (SequentFormula sf : semisequent) {
         SyntacticalReplaceVisitor visitor = new SyntacticalReplaceVisitor(services, svInst);
         sf.formula().execPostOrder(visitor);
         terms = terms.append(visitor.getTerm());
      }
      return terms;
   }

   /**
    * Returns the default choice value.
    * <b>Attention: </b> This method returns {@code null} if it is called before
    * a proof is instantiated the first time. It can be checked via
    * {@link #isChoiceSettingInitialised()}.
    * @param key The choice key.
    * @return The choice value.
    */
   public static String getChoiceSetting(String key) {
      Map<String, String> settings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
      return settings.get(key);
   }
   
   /**
    * Sets the default choice value.
    * <b>Attention: </b> Settings should not be changed before the first proof
    * is instantiated in KeY. Otherwise the default settings are not loaded.
    * If default settings are defined can be checked via {@link #isChoiceSettingInitialised()}.
    * @param key The choice key to modify.
    * @param value The new choice value to set.
    */
   public static void setChoiceSetting(String key, String value) {
      HashMap<String, String> settings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
      HashMap<String, String> clone = new HashMap<String, String>();
      clone.putAll(settings);
      clone.put(key, value);
      ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().setDefaultChoices(clone);
   }

   /**
    * Checks if the choice settings are initialized.
    * @return {@code true} settings are initialized, {@code false} settings are not initialized.
    */
   public static boolean isChoiceSettingInitialised() {
      return !ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices().isEmpty();
   }

   /**
    * This method should be called before the auto mode is started in
    * context of symbolic execution. The method sets {@link StrategyProperties}
    * of the auto mode which are not supported in context of symbolic execution
    * to valid default values.
    * @param proof The {@link Proof} to configure its {@link StrategyProperties} for symbolic execution.
    */
   public static void updateStrategyPropertiesForSymbolicExecution(Proof proof) {
      if (proof != null) {
         StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties(); 
         sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_DEFAULT);
         proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
      }
   }
}
