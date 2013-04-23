// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.util;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
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
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
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
import de.uka.ilkd.key.logic.op.Junctor;
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
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionElement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
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
      if (openGoals.isEmpty()) {
         return TermBuilder.DF.tt();
      }
      else {
         ImmutableList<Term> goalImplications = ImmutableSLList.nil(); 
         for (Goal goal : openGoals) {
            Term goalImplication = sequentToImplication(goal.sequent());
            goalImplication = TermBuilder.DF.not(goalImplication);
            goalImplications = goalImplications.append(goalImplication);
         }
         return TermBuilder.DF.not(TermBuilder.DF.or(goalImplications));
      }
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
      // Create Sequent to prove with new succedent.
      Sequent sequentToProve = createSequentToProveWithNewSuccedent(node, modalityTerm);
      // Return created sequent and the used predicate to identify the value interested in.
      return new SiteProofVariableValueInput(sequentToProve, newPredicate);
   }

   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param services The {@link Services} to use.
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param additionalConditions Optional additional conditions.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   public static SiteProofVariableValueInput createExtractVariableValueSequent(Services services,
                                                                               Node node,
                                                                               Term additionalConditions,
                                                                               IProgramVariable variable) {
      // Make sure that correct parameters are given
      assert node != null;
      assert variable instanceof ProgramVariable;
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(TermBuilder.DF.newName(services, "ResultPredicate")), Sort.FORMULA, variable.sort());
      // Create formula which contains the value interested in.
      Term newTerm = TermBuilder.DF.func(newPredicate, TermBuilder.DF.var((ProgramVariable)variable));
      // Create Sequent to prove with new succedent.
      Sequent sequentToProve = createSequentToProveWithNewSuccedent(node, additionalConditions, newTerm);
      // Return created sequent and the used predicate to identify the value interested in.
      return new SiteProofVariableValueInput(sequentToProve, newPredicate);
   }

   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param services The {@link Services} to use.
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param additionalConditions Additional conditions to add to the antecedent.
    * @param term The new succedent term.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   public static SiteProofVariableValueInput createExtractTermSequent(Services services,
                                                                      Node node,
                                                                      Term additionalConditions,
                                                                      Term term) {
      // Make sure that correct parameters are given
      assert node != null;
      assert term != null;
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(TermBuilder.DF.newName(services, "ResultPredicate")), Sort.FORMULA, term.sort());
      // Create formula which contains the value interested in.
      Term newTerm = TermBuilder.DF.func(newPredicate, term);
      // Create Sequent to prove with new succedent.
      Sequent sequentToProve = createSequentToProveWithNewSuccedent(node, additionalConditions, newTerm);
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
      return startSideProof(proof, sequentToProve, StrategyProperties.SPLITTING_OFF);
   }
   
   /**
    * Starts a site proof for the given {@link Sequent}.
    * @param proof The parent {@link Proof} of the site proof to do.
    * @param sequentToProve The {@link Sequent} to prove.
    * @return The proof result represented as {@link ApplyStrategyInfo} instance.
    * @throws ProofInputException Occurred Exception
    */
   public static ApplyStrategyInfo startSideProof(Proof proof,
                                                  Sequent sequentToProve,
                                                  String splittingOption) throws ProofInputException {
      ProofStarter starter = createSideProof(proof, sequentToProve);
      return startSideProof(proof, starter, splittingOption);
   }
   
   /**
    * Creates a new {@link ProofStarter} which contains a new site proof
    * of the given {@link Proof}.
    * @param proof The given {@link Proof}.
    * @param sequentToProve The {@link Sequent} to proof in a new site proof.
    * @return The created {@link ProofStarter} with the site proof.
    * @throws ProofInputException Occurred Exception.
    */
   public static ProofStarter createSideProof(Proof proof,
                                              Sequent sequentToProve) throws ProofInputException {
      // Make sure that valid parameters are given
      assert sequentToProve != null;
      // Create ProofStarter
      ProofStarter starter = new ProofStarter();
      // Configure ProofStarter
      ProofEnvironment env = SymbolicExecutionUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(proof); // New OneStepSimplifier is required because it has an internal state and the default instance can't be used parallel.
      starter.init(sequentToProve, env);
      return starter;
   }
   
   /**
    * Starts a site proof.
    * @param proof The original {@link Proof}.
    * @param starter The {@link ProofStarter} with the site proof.
    * @param splittingOption The splitting option to use.
    * @return The site proof result.
    */
   public static ApplyStrategyInfo startSideProof(Proof proof, ProofStarter starter, String splittingOption) {
      assert starter != null;
      starter.setMaxRuleApplications(1000);
      StrategyProperties sp = !proof.isDisposed() ? 
                              proof.getSettings().getStrategySettings().getActiveStrategyProperties() : // Is a clone that can be modified
                              new StrategyProperties();
      sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, splittingOption); // Logical Splitting: Off is faster and avoids splits, but Normal allows to determine that two objects are different.
      sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_NONE); // Method Treatment: Off
      sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_OFF); // Dependency Contracts: Off
      sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_OFF); // Query Treatment: Off
      sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS); // Arithmetic Treatment: DefOps
      sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING); // Quantifier treatment: No Splits 
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
   public static Term extractOperatorValue(ApplyStrategyInfo info, Operator operator) throws ProofInputException {
      // Make sure that valid parameters are given
      assert info != null;
      if (info.getProof().openGoals().size() != 1) {
         throw new ProofInputException("Assumption that return value extraction has one goal does not hold because " + info.getProof().openGoals().size() + " goals are available.");
      }
      // Get node of open goal
      return extractOperatorValue(info.getProof().openGoals().head(), operator);
   }

   /**
    * Extracts the value for the formula with the given {@link Operator}
    * from the given {@link Goal}.
    * @param goal The {@link Goal} to search the {@link Operator} in.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The value of the formula with the given {@link Operator}.
    */
   public static Term extractOperatorValue(Goal goal, final Operator operator) {
      assert goal != null;
      return extractOperatorValue(goal.node(), operator);
   }

   /**
    * Extracts the value for the formula with the given {@link Operator}
    * from the given {@link Node}.
    * @param node The {@link Node} to search the {@link Operator} in.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The value of the formula with the given {@link Operator}.
    */
   public static Term extractOperatorValue(Node node, final Operator operator) {
      Term operatorTerm = extractOperatorTerm(node, operator);
      return operatorTerm != null ? operatorTerm.sub(0) : null;
   }
   
   /**
    * Extracts the operator term for the formula with the given {@link Operator}
    * from the site proof result ({@link ApplyStrategyInfo}).
    * @param info The site proof result.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The operator term of the formula with the given {@link Operator}.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term extractOperatorTerm(ApplyStrategyInfo info, Operator operator) throws ProofInputException {
      // Make sure that valid parameters are given
      assert info != null;
      if (info.getProof().openGoals().size() != 1) {
         throw new ProofInputException("Assumption that return value extraction has one goal does not hold because " + info.getProof().openGoals().size() + " goals are available.");
      }
      // Get node of open goal
      return extractOperatorTerm(info.getProof().openGoals().head(), operator);
   }

   /**
    * Extracts the operator term for the formula with the given {@link Operator}
    * from the given {@link Goal}.
    * @param goal The {@link Goal} to search the {@link Operator} in.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The operator term of the formula with the given {@link Operator}.
    */
   public static Term extractOperatorTerm(Goal goal, final Operator operator) {
      assert goal != null;
      return extractOperatorTerm(goal.node(), operator);
   }

   /**
    * Extracts the operator term for the formula with the given {@link Operator}
    * from the given {@link Node}.
    * @param node The {@link Node} to search the {@link Operator} in.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The operator term of the formula with the given {@link Operator}.
    */
   public static Term extractOperatorTerm(Node node, final Operator operator) {
      assert node != null;
      // Search formula with the given operator in sequent
      SequentFormula sf = JavaUtil.search(node.sequent(), new IFilter<SequentFormula>() {
         @Override
         public boolean select(SequentFormula element) {
            return JavaUtil.equals(element.formula().op(), operator);
         }
      });
      if (sf != null) {
         return sf.formula();
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
            result[i] = new ExecutionVariable(node, var);
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
               ProgramVariable attribute = getProgramVariable(services, heapLDT, locationTerm);
               if (attribute != null && attribute.isStatic()) {
                  result.add(attribute);
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
    * Returns the {@link ProgramVariable} defined by the given {@link Term}.
    * @param services The {@link Services} to use.
    * @param heapLDT The {@link HeapLDT} to use.
    * @param locationTerm The {@link Term} to extract {@link ProgramVariable} from.
    * @return The {@link Term}s {@link ProgramVariable} or {@code null} if not available.
    */
   public static ProgramVariable getProgramVariable(Services services, HeapLDT heapLDT, Term locationTerm) {
      ProgramVariable result = null;
      if (locationTerm.op() instanceof Function) {
         Function function = (Function)locationTerm.op();
         // Make sure that the function is not an array
         if (heapLDT.getArr() != function) {
            String typeName = heapLDT.getClassName(function);
            KeYJavaType type = services.getJavaInfo().getKeYJavaType(typeName);
            if (type != null) {
               String fieldName = heapLDT.getPrettyFieldName(function);
               result = services.getJavaInfo().getAttribute(fieldName, type);
            }
         }
      }
      return result;
   }

   /**
    * Returns the array index defined by the given {@link Term}.
    * @param services The {@link Services} to use.
    * @param heapLDT The {@link HeapLDT} to use.
    * @param arrayIndexTerm The {@link Term} to extract the array index from.
    * @return The array index or {@code -1} if the term defines no array index.
    */
   public static int getArrayIndex(Services services, HeapLDT heapLDT, Term arrayIndexTerm) {
      // Make sure that the term is an array index
      if (arrayIndexTerm.op() == heapLDT.getArr() && arrayIndexTerm.subs().size() == 1) {
         Term sub = arrayIndexTerm.sub(0);
         // Make sure that the defined index is an integer
         if (services.getTypeConverter().getIntegerLDT().getNumberSymbol() == sub.op()) {
            return Integer.parseInt(ProofSaver.printAnything(sub, services));
         }
         else {
            return -1;
         }
      }
      else {
         return -1;
      }
   }

   /**
    * Searches the {@link IProgramVariable} of the current {@code this}/{@code self} reference.
    * @param node The {@link Node} to search in.
    * @return The found {@link IProgramVariable} with the current {@code this}/{@code self} reference or {@code null} if no one is available.
    */
   public static IProgramVariable findSelfTerm(Node node) {
      Term term = node.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
      term = TermBuilder.DF.goBelowUpdates(term);
      JavaBlock jb = term.javaBlock();
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
               if (isImplicitConstructor(pm)) {
                  IProgramMethod explicitConstructor = findExplicitConstructor(node.proof().getServices(), pm);
                  return explicitConstructor != null && 
                         !isLibraryClass(explicitConstructor.getContainerType());
               }
               else {
                  return !pm.isImplicit(); // Do not include implicit methods, but always constructors
               }
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
    * Checks if the given {@link KeYJavaType} is a library class.
    * @param kjt The {@link KeYJavaType} to check.
    * @return {@code true} is library class, {@code false} is no library class.
    */
   public static boolean isLibraryClass(KeYJavaType kjt) {
      return kjt != null && 
             kjt.getJavaType() instanceof TypeDeclaration && 
             ((TypeDeclaration)kjt.getJavaType()).isLibraryClass();
   }
   
   /**
    * Checks if the given {@link IProgramMethod} is an implicit constructor.
    * @param pm The {@link IProgramMethod} to check.
    * @return {@code true} is implicit constructor, {@code false} is no implicit constructor (e.g. method or explicit construcotr).
    */
   public static boolean isImplicitConstructor(IProgramMethod pm) {
      return pm != null && ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER.equals(pm.getName());
   }

   /**
    * Returns the {@link IProgramMethod} of the explicit constructor for
    * the given implicit constructor.
    * @param services The {@link Services} to use.
    * @param implicitConstructor The implicit constructor.
    * @return The found explicit constructor or {@code null} if not available.
    */
   public static IProgramMethod findExplicitConstructor(Services services, final IProgramMethod implicitConstructor) {
      if (services != null && implicitConstructor != null) {
         ImmutableList<IProgramMethod> pms = services.getJavaInfo().getConstructors(implicitConstructor.getContainerType());
         return JavaUtil.search(pms, new IFilter<IProgramMethod>() {
            @Override
            public boolean select(IProgramMethod element) {
               if (implicitConstructor.getParameterDeclarationCount() == element.getParameterDeclarationCount()) {
                  Iterator<ParameterDeclaration> implicitIter = implicitConstructor.getParameters().iterator();
                  Iterator<ParameterDeclaration> elementIter = element.getParameters().iterator();
                  boolean sameTypes = true;
                  while (sameTypes && implicitIter.hasNext() && elementIter.hasNext()) {
                     ParameterDeclaration implicitNext = implicitIter.next();
                     ParameterDeclaration elementNext = elementIter.next();
                     sameTypes = implicitNext.getTypeReference().equals(elementNext.getTypeReference());
                  }
                  return sameTypes;
               }
               else {
                  return false;
               }
            }
         });
      }
      else {
         return null;
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
             posInfo.getEndPosition().getLine() >= 0 &&  // Filter out statements where source code is missing.
             !(statement instanceof EmptyStatement) && // Filter out empty statements
             !(statement instanceof StatementBlock && ((StatementBlock)statement).isEmpty()); // FIlter out empty blocks
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
    * Checks if the given node should be represented as use operation contract.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} represent node as use operation contract, {@code false} represent node as something else. 
    */
   public static boolean isUseOperationContract(Node node, RuleApp ruleApp) {
      return "Use Operation Contract".equals(MiscTools.getRuleDisplayName(ruleApp));
   }

   /**
    * Checks if the given node should be represented as loop invariant.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} represent node as use loop invariant, {@code false} represent node as something else. 
    */
   public static boolean isUseLoopInvariant(Node node, RuleApp ruleApp) {
      return "Loop Invariant".equals(MiscTools.getRuleDisplayName(ruleApp));
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
      if (node != null && !isRuleAppToIgnore(ruleApp)) {
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
         else if (isUseOperationContract(node, ruleApp)) {
            return true;
         }
         else if (isUseLoopInvariant(node, ruleApp)) {
            return true;
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
    * Checks if the given {@link RuleApp} should be ignored or
    * checked for possible symbolic execution tree node representation.
    * @param ruleApp The {@link RuleApp} to check.
    * @return {@code true} ignore {@link RuleApp}, {@code false} check if the {@link RuleApp} represents a symbolic execution tree node. 
    */
   public static boolean isRuleAppToIgnore(RuleApp ruleApp) {
      return "unusedLabel".equals(MiscTools.getRuleDisplayName(ruleApp));
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
    * @param simplify {@code true} simplify result, {@code false} keep computed non simplified result.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term computeBranchCondition(Node node, boolean simplify) throws ProofInputException {
      // Get applied taclet on parent proof node
      Node parent = node.parent();
      if (parent.getAppliedRuleApp() instanceof TacletApp) {
         return computeTacletAppBranchCondition(parent, node, simplify);
      }
      else if (parent.getAppliedRuleApp() instanceof ContractRuleApp) {
        return computeContractRuleAppBranchCondition(parent, node, simplify);
      }
      else if (parent.getAppliedRuleApp() instanceof LoopInvariantBuiltInRuleApp) {
         return TermBuilder.DF.tt(); // TODO: Implement real branch condition of loop invariants!
      }
      else {
         throw new ProofInputException("Unsupported RuleApp in branch computation \"" + parent.getAppliedRuleApp() + "\"."); 
      }
   }
   
   /**
    * <p>
    * Computes the branch condition of the given {@link Node} which was constructed by a {@link ContractRuleApp}.
    * </p>
    * <p>
    * The branch conditions are:
    * <ul>
    *    <li>Post:    (pre1 | .. | preN)</li>
    *    <li>ExcPost: (excPre1 | ... | excPreM)</li>
    *    <li>Pre:     !(pre1 | ... | preN | excPre1 | ... | excPreM)</li>
    *    <li>NPE:     caller = null</li>
    * </ul>
    * </p>
    * <p>
    * Idea:
    * <ul>
    *    <li>Last semisequent in antecedent contains contract</li>
    *    <li>Contract is defined as {@code exc_0 = null} and {@code pre -> post}/{@code excPre -> !exc_0 = null & signals} terms</li>
    *    <li>Find {@code exc_0 = null} Term</li>
    *    <li>List all implications</li>
    *    <li>Filter implications for post/exceptional post branch based on the negation of {@code exc_0 = null}</li>
    *    <li>Return disjunction of all filtered implication conditions or return true if no implications were found</li>
    * </ul>
    * </p>
    * @param parent The parent {@link Node} of the given one.
    * @param node The {@link Node} to compute its branch condition.
    * @param simplify {@code true} simplify result, {@code false} keep computed non simplified result.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   private static Term computeContractRuleAppBranchCondition(Node parent, Node node, boolean simplify) throws ProofInputException {
      // Make sure that a computation is possible
      if (!(parent.getAppliedRuleApp() instanceof ContractRuleApp)) {
         throw new ProofInputException("Only ContractRuleApp is allowed in branch computation but rule \"" + parent.getAppliedRuleApp() + "\" was found."); 
      }
      
      int childIndex = JavaUtil.indexOf(parent.childrenIterator(), node);
      if (childIndex >= 2) {
         throw new ProofInputException("Branch condition of precondition check and null pointer check are not supported."); 
      }
      // Assumption: Pre -> Post & ExcPre -> Signals terms are added to last semisequent in antecedent.
      // Find Term to extract implications from.
      Semisequent antecedent = node.sequent().antecedent();
      SequentFormula sf = antecedent.get(antecedent.size() - 1);
      Term workingTerm = sf.formula();
      workingTerm = TermBuilder.DF.goBelowUpdates(workingTerm);
      if (workingTerm.op() != Junctor.AND) {
         throw new ProofInputException("And operation expacted, implementation of UseOperationContractRule might has changed!"); 
      }
      workingTerm = workingTerm.sub(1); // First part is heap equality, use second part which is the combination of all normal and exceptional preconditon postcondition implications
      workingTerm = TermBuilder.DF.goBelowUpdates(workingTerm);
      if (workingTerm.op() != Junctor.AND) {
         throw new ProofInputException("And operation expacted, implementation of UseOperationContractRule might has changed!"); 
      }
      // Find Term exc_n = null which is added negated to all exceptional preconditions
      Term definitions = workingTerm.sub(0);
      if (definitions.op() != Junctor.AND) {
         throw new ProofInputException("And operation expacted, implementation of UseOperationContractRule might has changed!"); 
      }
      Term exceptionDefinition = definitions.sub(0);
      // Collect all implications for normal or exceptional preconditions
      Term implications = workingTerm.sub(1);
      ImmutableList<Term> implicationTerms = collectPreconditionImpliesPostconditionTerms(ImmutableSLList.<Term>nil(), exceptionDefinition, childIndex == 1, implications);
      if (!implicationTerms.isEmpty()) {
         // Implications find, return their conditions as branchconditions
         ImmutableList<Term> condtionTerms = ImmutableSLList.<Term>nil();
         for (Term implication : implicationTerms) {
            condtionTerms = condtionTerms.append(implication.sub(0));
         }
         
         Term result = TermBuilder.DF.or(condtionTerms);
         if (simplify) {
            workingTerm = simplify(node.proof(), result);
         }
         return result;
      }
      else {
         // No preconditions available, branchcondition is true
         return TermBuilder.DF.tt();
      }
   }

   /**
    * Lists recursive implications filtered for post or exceptional post branch.
    * @param toFill The result {@link ImmutableList} to fill.
    * @param exceptionDefinition The exception definition {@code exc_0 = null}.
    * @param exceptionalExecution {@code true} exceptional post branch, {@code false} post branch.
    * @param root The root {@link Term} to start search in.
    * @return The found implications.
    */
   private static ImmutableList<Term> collectPreconditionImpliesPostconditionTerms(ImmutableList<Term> toFill,
                                                                                   Term exceptionDefinition,
                                                                                   boolean exceptionalExecution,
                                                                                   Term root) {
      if (root.op() == Junctor.IMP) {
         // Check if first condition is the exceptional definition
         boolean isExceptionCondition = false;
         Term toCheck = root.sub(1);
         while (!isExceptionCondition && !toCheck.subs().isEmpty()) {
            // Assumption: Implications implies first that exception is not null 
            if (toCheck == exceptionDefinition) {
               isExceptionCondition = true;
            }
            toCheck = toCheck.sub(0);
         }
         // Update result
         if (exceptionalExecution) {
            if (isExceptionCondition) {
               toFill = toFill.append(root);
            }
         }
         else {
            if (!isExceptionCondition) {
               toFill = toFill.append(root);
            }
         }
      }
      else {
         for (Term sub : root.subs()) {
            toFill = collectPreconditionImpliesPostconditionTerms(toFill, exceptionDefinition, exceptionalExecution, sub);
         }
      }
      return toFill;
   }

   /**
    * Computes the branch condition of the given {@link Node} which was constructed by a {@link TacletApp}.
    * @param parent The parent {@link Node} of the given one.
    * @param node The {@link Node} to compute its branch condition.
    * @param simplify {@code true} simplify result, {@code false} keep computed non simplified result.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   private static Term computeTacletAppBranchCondition(Node parent, Node node, boolean simplify) throws ProofInputException {
      if (!(parent.getAppliedRuleApp() instanceof TacletApp)) {
         throw new ProofInputException("Only TacletApp is allowed in branch computation but rule \"" + parent.getAppliedRuleApp() + "\" was found."); 
      }
      TacletApp app = (TacletApp)parent.getAppliedRuleApp();
      // Find goal template which has created the represented proof node
      int childIndex = JavaUtil.indexOf(parent.childrenIterator(), node);
      TacletGoalTemplate goalTemplate = app.taclet().goalTemplates().take(app.taclet().goalTemplates().size() - 1 - childIndex).head();
      // Apply instantiations of schema variables to sequent of goal template
      Services services = node.proof().getServices();
      SVInstantiations instantiations = app.instantiations();
      // List additions
      ImmutableList<Term> antecedents = listSemisequentTerms(services, instantiations, goalTemplate.sequent().antecedent());
      ImmutableList<Term> succedents = listSemisequentTerms(services, instantiations, goalTemplate.sequent().succedent());
      // List replacements
      if (!NodeInfo.isSymbolicExecution(app.taclet())) {
         if (goalTemplate.replaceWithExpressionAsObject() instanceof Sequent) {
            antecedents = antecedents.append(listSemisequentTerms(services, instantiations, ((Sequent)goalTemplate.replaceWithExpressionAsObject()).antecedent()));
            succedents = succedents.append(listSemisequentTerms(services, instantiations, ((Sequent)goalTemplate.replaceWithExpressionAsObject()).succedent()));
         }
         else if (goalTemplate.replaceWithExpressionAsObject() instanceof Term) {
            // Make sure that an PosTacletApp was applied
            if (!(app instanceof PosTacletApp)) {
               throw new ProofInputException("Only PosTacletApp are allowed with a replace term in branch computation but rule \"" + app + "\" was found."); 
            }
            // Create new lists
            ImmutableList<Term> newAntecedents = ImmutableSLList.nil();
            ImmutableList<Term> newSuccedents = ImmutableSLList.nil();
            // Apply updates on antecedents and add result to new antecedents list
            for (Term a : antecedents) {
               newAntecedents = newAntecedents.append(TermBuilder.DF.applySequential(app.instantiations().getUpdateContext(), a));
            }
            // Apply updates on succedents and add result to new succedents list
            for (Term suc : succedents) {
               newSuccedents = newSuccedents.append(TermBuilder.DF.applySequential(app.instantiations().getUpdateContext(), suc));
            }
            // Add additional equivalenz term to antecedent with the replace object which must be equal to the find term 
            Term replaceTerm = (Term)goalTemplate.replaceWithExpressionAsObject();
            replaceTerm = TermBuilder.DF.equals(replaceTerm, ((PosTacletApp)app).posInOccurrence().subTerm());
            replaceTerm = TermBuilder.DF.applySequential(app.instantiations().getUpdateContext(), replaceTerm);
            newAntecedents = newAntecedents.append(replaceTerm);
            // Replace old with new lists
            antecedents = newAntecedents;
            succedents = newSuccedents;
         }
         else {
            throw new ProofInputException("Expected replacement as Sequent during branch condition computation but is \"" + goalTemplate.replaceWithExpressionAsObject() + "\".");
         }
      }
      // Construct branch condition from created antecedent and succedent terms as new implication 
      Term left = TermBuilder.DF.and(antecedents);
      Term right = TermBuilder.DF.or(succedents);
      Term leftAndRight = TermBuilder.DF.and(left, TermBuilder.DF.not(right));
      Term result;
      // Check if an update context is available
      if (!instantiations.getUpdateContext().isEmpty()) {
         // Simplify branch condition if required
         if (simplify) {
            // Append update context because otherwise the formula is evaluated in wrong state
            result = TermBuilder.DF.applySequential(instantiations.getUpdateContext(), leftAndRight);
            // Execute simplification
            result = SymbolicExecutionUtil.simplify(node.proof(), result);
         }
         else {
            result = leftAndRight;
         }
      }
      else {
         // No update context, just use the implication as branch condition
         result = leftAndRight;
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

   /**
    * Checks if the given {@link Term} is null in the {@link Sequent} of the given {@link Node}. 
    * @param services The {@link Services} to use.
    * @param node The {@link Node} which provides the original {@link Sequent}
    * @param additionalAntecedent An additional antecedent.
    * @param newSuccedent The {@link Term} to check.
    * @return {@code true} {@link Term} was evaluated to null, {@code false} {@link Term} was not evaluated to null.
    * @throws ProofInputException Occurred Exception
    */
   public static boolean isNull(Services services, 
                                Node node, 
                                Term additionalAntecedent, 
                                Term newSuccedent) throws ProofInputException {
      return checkNull(services, node, additionalAntecedent, newSuccedent, true);
   }

   /**
    * Checks if the given {@link Term} is not null in the {@link Sequent} of the given {@link Node}. 
    * @param services The {@link Services} to use.
    * @param node The {@link Node} which provides the original {@link Sequent}
    * @param additionalAntecedent An additional antecedent.
    * @param newSuccedent The {@link Term} to check.
    * @return {@code true} {@link Term} was evaluated to not null, {@code false} {@link Term} was not evaluated to not null.
    * @throws ProofInputException Occurred Exception
    */
   public static boolean isNotNull(Services services, 
                                   Node node, 
                                   Term additionalAntecedent, 
                                   Term newSuccedent) throws ProofInputException {
      return checkNull(services, node, additionalAntecedent, newSuccedent, false);
   }
   
   /**
    * Checks if the given {@link Term} is null or not in the {@link Sequent} of the given {@link Node}.
    * @param services The {@link Services} to use.
    * @param node The {@link Node} which provides the original {@link Sequent}
    * @param additionalAntecedent An additional antecedent.
    * @param newSuccedent The {@link Term} to check.
    * @param nullExpected {@code true} expect that {@link Term} is null, {@code false} expect that term is not null.
    * @return {@code true} term is null value matches the expected nullExpected value, {@code false} otherwise.
    * @throws ProofInputException Occurred Exception
    */
   private static boolean checkNull(Services services, 
                                    Node node, 
                                    Term additionalAntecedent, 
                                    Term newSuccedent,
                                    boolean nullExpected) throws ProofInputException {
      // Make sure that correct parameters are given
      assert node != null;
      assert newSuccedent != null;
      // Create Sequent to prove
      Term isNull = TermBuilder.DF.equals(newSuccedent, TermBuilder.DF.NULL(services));
      Term isNotNull = TermBuilder.DF.not(isNull);
      Sequent sequentToProve = createSequentToProveWithNewSuccedent(node, additionalAntecedent, nullExpected ? isNull : isNotNull);
      // Execute proof in the current thread
      ApplyStrategyInfo info = startSideProof(node.proof(), sequentToProve, StrategyProperties.SPLITTING_NORMAL);
      return !info.getProof().openEnabledGoals().isEmpty();
   }
   
   /**
    * Creates a new {@link Sequent} which is a modification from the {@link Sequent}
    * of the given {@link Node} which contains the same information but a different succedent.
    * @param node The {@link Node} which provides the original {@link Sequent}.
    * @param newSuccedent The new succedent.
    * @return The created {@link Sequent}.
    */
   public static Sequent createSequentToProveWithNewSuccedent(Node node,
                                                              Term newSuccedent) {
      return createSequentToProveWithNewSuccedent(node, null, newSuccedent);
   }

   /**
    * Creates a new {@link Sequent} which is a modification from the {@link Sequent}
    * of the given {@link Node} which contains the same information but a different succedent.
    * @param node The {@link Node} which provides the original {@link Sequent}.
    * @param additionalAntecedent An optional additional antecedents.
    * @param newSuccedent The new succedent.
    * @return The created {@link Sequent}.
    */
   public static Sequent createSequentToProveWithNewSuccedent(Node node, 
                                                              Term additionalAntecedent,
                                                              Term newSuccedent) {
      // Get the updates from the return node which includes the value interested in.
      Term originalModifiedFormula = node.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
      ImmutableList<Term> originalUpdates = TermBuilder.DF.goBelowUpdates2(originalModifiedFormula).first;
      // Create new sequent
      return createSequentToProveWithNewSuccedent(node, additionalAntecedent, newSuccedent, originalUpdates);
   }
   
   /**
    * Creates a new {@link Sequent} which is a modification from the {@link Sequent}
    * of the given {@link Node} which contains the same information but a different succedent.
    * @param node The {@link Node} which provides the original {@link Sequent}.
    * @param additionalAntecedent An optional additional antecedents.
    * @param newSuccedent The new succedent.
    * @param updates The updates to use.
    * @return The created {@link Sequent}.
    */
   public static Sequent createSequentToProveWithNewSuccedent(Node node, 
                                                              Term additionalAntecedent,
                                                              Term newSuccedent,
                                                              ImmutableList<Term> updates) {
      // Combine method frame, formula with value predicate and the updates which provides the values
      Term newSuccedentToProve = TermBuilder.DF.applySequential(updates, newSuccedent);
      // Create new sequent with the original antecedent and the formulas in the succedent which were not modified by the applied rule
      PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
      Sequent originalSequentWithoutMethodFrame = node.sequent().removeFormula(pio).sequent();
      Sequent sequentToProve = originalSequentWithoutMethodFrame.addFormula(new SequentFormula(newSuccedentToProve), false, true).sequent();
      if (additionalAntecedent != null) {
         sequentToProve = sequentToProve.addFormula(new SequentFormula(additionalAntecedent), true, false).sequent();
      }
      return sequentToProve;
   }

   /**
    * Checks if the given {@link Sort} represents a {@code null} value in the given {@link Services}.
    * @param sort The {@link Sort} to check.
    * @param services The {@link Services} to use.
    * @return {@code true} is Null-Sort, {@code false} is something else.
    */
   public static boolean isNullSort(Sort sort, Services services) {
      if (sort != null && services != null) {
         JavaInfo javaInfo = services.getJavaInfo();
         return javaInfo.getKeYJavaType(sort) == javaInfo.getNullType();
      }
      else {
         return false;
      }
   }

   /**
    * Checks if the given {@link IProgramVariable} is static or not.
    * @return {@code true} is static, {@code false} is not static or is array cell.
    */
   public static boolean isStaticVariable(IProgramVariable programVariable) {
      return programVariable instanceof ProgramVariable &&
             ((ProgramVariable)programVariable).isStatic();
   }
   
   /**
    * Collects all {@link IProgramVariable}s of the given {@link FieldDeclaration}.
    * @param fd The given {@link FieldDeclaration}.
    * @return The found {@link IProgramVariable}s for the given {@link FieldDeclaration}.
    */
   public static Set<IProgramVariable> getProgramVariables(FieldDeclaration fd) {
      Set<IProgramVariable> result = new LinkedHashSet<IProgramVariable>();
      if (fd != null) {
         ImmutableArray<FieldSpecification> specifications = fd.getFieldSpecifications();
         for (FieldSpecification spec : specifications) {
            result.add(spec.getProgramVariable());
         }
      }
      return result;
   }

   /**
    * Computes the path condition of the given {@link Node}.
    * @param node The {@link Node} to compute its path condition.
    * @param simplify {@code true} simplify result, {@code false} keep computed non simplified result.
    * @return The computed path condition.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term computePathCondition(Node node, boolean simplify) throws ProofInputException {
      if (node != null) {
         Term pathCondition = TermBuilder.DF.tt();
         while (node != null) {
            Node parent = node.parent();
            if (parent != null && parent.childrenCount() >= 2) {
               Term branchCondition = computeBranchCondition(node, simplify);
               pathCondition = TermBuilder.DF.and(branchCondition, pathCondition);
            }
            node = parent;
         }
         if (TermBuilder.DF.ff().equals(pathCondition)) {
            throw new ProofInputException("Path condition computation failed because the result is false.");
         }
         return pathCondition;
      }
      else {
         return null;
      }
   }

   /**
    * Checks if the {@link Sort} of the given {@link Term} is a reference type.
    * @param services The {@link Services} to use.
    * @param term The {@link Term} to check.
    * @return {@code true} is reference sort, {@code false} is no reference sort.
    */
   public static boolean hasReferenceSort(Services services, Term term) {
      if (services != null && term != null) {
         return hasReferenceSort(services, term.sort());
      }
      else {
         return false;
      }
   }

   /**
    * Checks if the {@link Sort} of the given {@link IProgramVariable} is a reference type.
    * @param services The {@link Services} to use.
    * @param var The {@link IProgramVariable} to check.
    * @return {@code true} is reference sort, {@code false} is no reference sort.
    */
   public static boolean hasReferenceSort(Services services, IProgramVariable var) {
      if (services != null && var != null) {
         return hasReferenceSort(services, var.sort());
      }
      else {
         return false;
      }
   }

   /**
    * Checks if the {@link Sort} is a reference type.
    * @param services The {@link Services} to use.
    * @param sort The {@link Sort} to check.
    * @return {@code true} is reference sort, {@code false} is no reference sort.
    */
   public static boolean hasReferenceSort(Services services, Sort sort) {
      boolean referenceSort = false;
      if (services != null && sort != null) {
         KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sort);
         if (kjt != null) {
            TypeConverter typeConverter = services.getTypeConverter();
            referenceSort = typeConverter.isReferenceType(kjt) && // Check if the value is a reference type
                            (!(kjt.getJavaType() instanceof TypeDeclaration) || // check if the value is a library class which should be ignored
                            !((TypeDeclaration)kjt.getJavaType()).isLibraryClass());
         }
      }
      return referenceSort;
   }
   
   /**
    * Returns the human readable name of the given {@link IProgramVariable}.
    * @param pv The {@link IProgramVariable} to get its name.
    * @return The human readable name of the given {@link IProgramVariable}.
    */
   public static String getDisplayString(IProgramVariable pv) {
      if (pv != null) {
         if (pv.name() instanceof ProgramElementName) {
            ProgramElementName name = (ProgramElementName)pv.name();
            if (SymbolicExecutionUtil.isStaticVariable(pv)) {
               return name.toString();
            }
            else {
               return name.getProgramName();
            }
         }
         else {
            return pv.name().toString();
         }
      }
      else {
         return null;
      }
   }

   /**
    * Returns the root of the given {@link IExecutionNode}.
    * @param executionNode The {@link IExecutionNode} to get the root of its symbolic execution tree.
    * @return The root of the given {@link IExecutionNode}.
    */
   public static IExecutionNode getRoot(IExecutionNode executionNode) {
      if (executionNode != null) {
         while (executionNode.getParent() != null) {
            executionNode = executionNode.getParent();
         }
         return executionNode;
      }
      else {
         return null;
      }
   }

   /**
    * Extracts the exception variable which is used to check if the executed program in proof terminates normally.
    * @param proof The {@link Proof} to extract variable from.
    * @return The extract variable.
    */
   public static IProgramVariable extractExceptionVariable(Proof proof) {
      Node root = proof.root();
      if (root.sequent().succedent().size() == 1) {
         Term succedent = root.sequent().succedent().getFirst().formula(); // Succedent term
         if (succedent.subs().size() == 2) {
            Term updateApplication = succedent.subs().get(1);
            if (updateApplication.subs().size() == 2) {
               JavaProgramElement updateContent = updateApplication.subs().get(1).javaBlock().program();
               if (updateContent instanceof StatementBlock) { // try catch inclusive
                  ImmutableArray<? extends Statement> updateContentBody = ((StatementBlock)updateContent).getBody();
                  if (updateContentBody.size() == 2 && updateContentBody.get(1) instanceof Try) {
                     Try tryStatement = (Try)updateContentBody.get(1);
                     if (tryStatement.getBranchCount() == 1 && tryStatement.getBranchList().get(0) instanceof Catch) {
                        Catch catchStatement = (Catch)tryStatement.getBranchList().get(0);
                        if (catchStatement.getBody() instanceof StatementBlock) {
                           StatementBlock  catchBlock = (StatementBlock)catchStatement.getBody();
                           if (catchBlock.getBody().size() == 1 && catchBlock.getBody().get(0) instanceof Assignment) {
                              Assignment assignment = (Assignment)catchBlock.getBody().get(0);
                              if (assignment.getFirstElement() instanceof IProgramVariable) {
                                 IProgramVariable var = (IProgramVariable)assignment.getFirstElement();
                                 return var;
                              }
                           }
                        }
                     }
                  }
               }
            }
         }
      }
      throw new IllegalStateException("Can't extract exception variable from proof.");
   }

   /**
    * Configures the proof to use operation contracts or to expand methods instead.
    * @param proof The {@link Proof} to configure.
    * @param useOperationContracts {@code true} use operation contracts, {@code false} expand methods.
    */
   public static void setUseOperationContracts(Proof proof, boolean useOperationContracts) {
      if (proof != null && !proof.isDisposed()) {
         String methodTreatmentValue = useOperationContracts ? 
                                       StrategyProperties.METHOD_CONTRACT : 
                                       StrategyProperties.METHOD_EXPAND;
         StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
         sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, methodTreatmentValue);
         proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
      }
   }

   /**
    * Configures the proof to use loop invariants or to expand loops instead.
    * @param proof The {@link Proof} to configure.
    * @param useLoopInvariants {@code true} use loop invariants, {@code false} expand loops.
    */
   public static void setUseLoopInvariants(Proof proof, boolean useLoopInvariants) {
      if (proof != null && !proof.isDisposed()) {
         String loopTreatmentValue = useLoopInvariants ? 
                                     StrategyProperties.LOOP_INVARIANT : 
                                     StrategyProperties.LOOP_EXPAND;
         StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
         sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, loopTreatmentValue);
         proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
      }
   }
   
   /**
    * Checks if the choice settings are initialized.
    * @return {@code true} settings are initialized, {@code false} settings are not initialized.
    */
   public static boolean isChoiceSettingInitialised() {
      return !ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getChoices().isEmpty();
   }
}
