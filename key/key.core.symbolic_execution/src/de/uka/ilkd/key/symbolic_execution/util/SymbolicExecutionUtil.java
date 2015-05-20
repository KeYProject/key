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

package de.uka.ilkd.key.symbolic_execution.util;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.expression.Assignment;
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
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.ExecutionVariableExtractor;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionElement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionVariable;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

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
    * Name of {@link #RESULT_LABEL}.
    */
   public static final Name RESULT_LABEL_NAME = new Name("RES");

   /**
    * Label attached to a {@link Term} to evaluate in a side proof.
    */
   public static final TermLabel RESULT_LABEL = new ParameterlessTermLabel(RESULT_LABEL_NAME);

   /**
    * Name of {@link #LOOP_BODY_LABEL}.
    */
   public static final Name LOOP_BODY_LABEL_NAME = new Name("LoopBody");

   /**
    * Label attached to the modality which executes a loop body in branch
    * "Body Preserves Invariant" of applied "Loop Invariant" rules.
    */
   public static final TermLabel LOOP_BODY_LABEL = new ParameterlessTermLabel(LOOP_BODY_LABEL_NAME);

   /**
    * Name of {@link #LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL}.
    */
   public static final Name LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL_NAME = new Name("LoopInvariantNormalBehavior");

   /**
    * Label attached to the implication when a loop body execution terminated
    * normally without any exceptions, returns or breaks in branch
    * "Body Preserves Invariant" of applied "Loop Invariant" rules to show the
    * loop invariant.
    */
   public static final TermLabel LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL =
           new ParameterlessTermLabel(LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL_NAME);

   /**
    * Forbid instances.
    */
   private SymbolicExecutionUtil() {
   }
   
   /**
    * Simplifies the given {@link Term} in a side proof. 
    * @param initConfig The {@link InitConfig} to use.
    * @param term The {@link Term} to simplify.
    * @return The simplified {@link Term}.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term simplify(InitConfig initConfig,
                               Term term) throws ProofInputException {
      return simplify(initConfig, null, term);
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
      assert !parentProof.isDisposed();
      return simplify(parentProof.getInitConfig(), parentProof, term);
   }
   
   /**
    * Simplifies the given {@link Term} in a side proof. 
    * @param initConfig The {@link InitConfig} to use.
    * @param parentProof The parent {@link Proof} which provides the {@link StrategySettings}.
    * @param term The {@link Term} to simplify.
    * @return The simplified {@link Term}.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term simplify(InitConfig initConfig,
                               Proof parentProof,
                               Term term) throws ProofInputException {
      final Services services = initConfig.getServices();
      final ProofEnvironment sideProofEnv = SymbolicExecutionSideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(initConfig, true); // New OneStepSimplifier is required because it has an internal state and the default instance can't be used parallel.
      // Create Sequent to prove
      Sequent sequentToProve = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(term), false, true).sequent();
      // Return created Sequent and the used predicate to identify the value interested in.
      ApplyStrategyInfo info = SymbolicExecutionSideProofUtil.startSideProof(parentProof, sideProofEnv, sequentToProve);
      try {
         // The simplified formula is the conjunction of all open goals
         ImmutableList<Goal> openGoals = info.getProof().openEnabledGoals();
         final TermBuilder tb = services.getTermBuilder();
         if (openGoals.isEmpty()) {
            return tb.tt();
         }
         else {
            ImmutableList<Term> goalImplications = ImmutableSLList.nil(); 
            for (Goal goal : openGoals) {
               Term goalImplication = sequentToImplication(goal.sequent(), goal.proof().getServices());
               goalImplication = tb.not(goalImplication);
               goalImplications = goalImplications.append(goalImplication);
            }
            return tb.not(tb.or(goalImplications));
         }
      }
      finally {
         SymbolicExecutionSideProofUtil.disposeOrStore("Simplification of " + ProofSaver.printAnything(term, services), info);
      }
   }

   /**
    * Converts the given {@link Sequent} into an implication.
    * @param sequent The {@link Sequent} to convert.
    * @param services The {@link Services} to use.
    * @return The created implication.
    */
   public static Term sequentToImplication(Sequent sequent, Services services) {
      if (sequent != null) {
         ImmutableList<Term> antecedents = listSemisequentTerms(sequent.antecedent());
         ImmutableList<Term> succedents = listSemisequentTerms(sequent.succedent());
         // Construct branch condition from created antecedent and succedent terms as new implication 
         Term left = services.getTermBuilder().and(antecedents);
         Term right = services.getTermBuilder().or(succedents);
         return services.getTermBuilder().imp(left, right);
      }
      else {
         return services.getTermBuilder().tt();
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
    * Improves the {@link Term} to increase its readability.
    * The following changes will be performed:
    * <ul>
    *    <li>{@code a < 1 + b} => {@code a <= b}</li>
    *    <li>{@code a < b + 1} => {@code a <= b}</li>
    *
    *    <li>{@code a >= 1 + b} => {@code a > b}</li>
    *    <li>{@code a >= b + 1} => {@code a > b}</li>
    *
    *    <li>{@code a <= -1 + b} => {@code a < b}</li>
    *    <li>{@code a <= b + -1} => {@code a < b}</li>
    *    <li>{@code a <= b - 1} => {@code a < b}</li>
    *
    *    <li>{@code a > -1 + b} => {@code a >= b}</li>
    *    <li>{@code a > b + -1} => {@code a >= b}</li>
    *    <li>{@code a > b - 1} => {@code a >= b}</li>
    *
    *    <li>{@code a >= 1 + b} => {@code a > b}</li>
    *    <li>{@code a >= b + 1} => {@code a > b}</li>
    *    <li>{@code !a >= b} => {@code a < b}</li>
    *    <li>{@code !a > b} => {@code a <= b}</li>
    *    <li>{@code !a <= b} => {@code a > b}</li>
    *    <li>{@code !a < b} => {@code a >= b}</li>
    * </ul>
    * @param term The {@link Term} to improve.
    * @param services The {@link Services} to use.
    * @return The improved {@link Term} or the {@link Term} itself if no improvements are possible.
    */
   public static Term improveReadability(Term term, Services services) {
      if (term != null && services != null) {
         IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
         term = improveReadabilityRecursive(term, services, integerLDT);
      }
      return term;
   }
   
   /**
    * Helper method of {@link #improveReadability(Term, Services)}.
    * @param term The {@link Term} to improve.
    * @param services The {@link Services} to use.
    * @param integerLDT The {@link IntegerLDT} to use.
    * @return The improved {@link Term} or the {@link Term} itself if no improvements are possible.
    */
   private static Term improveReadabilityRecursive(Term term,
                                                   Services services,
                                                   IntegerLDT integerLDT) {
      // Improve children
      boolean subChanged = false;
      List<Term> newSubs = new LinkedList<Term>();
      for (Term sub : term.subs()) {
         Term newSub = improveReadabilityRecursive(sub, services, integerLDT);
         if (newSub != sub) {
            newSubs.add(newSub);
            subChanged = true;
         }
         else {
            newSubs.add(sub);
         }
      }
      if (subChanged) {
         term = services.getTermFactory().createTerm(term.op(), new ImmutableArray<Term>(newSubs), term.boundVars(), term.javaBlock(), term.getLabels());
      }
      // Improve readability: a < 1 + b, a < b + 1
      final TermBuilder tb = services.getTermBuilder();
      if (term.op() == integerLDT.getLessThan()) {
         Term subOne = term.sub(1);
         if (subOne.op() == integerLDT.getAdd()) {
            if (isOne(subOne.sub(0), integerLDT)) {
               term = tb.leq(term.sub(0), subOne.sub(1));
            }
            else if (isOne(subOne.sub(1), integerLDT)) {
               term = tb.leq(term.sub(0), subOne.sub(0));
            }
         }
      }
      // Improve readability: a >= 1 + b, a >= b + 1
      else if (term.op() == integerLDT.getGreaterOrEquals()) {
         Term subOne = term.sub(1);
         if (subOne.op() == integerLDT.getAdd()) {
            if (isOne(subOne.sub(0), integerLDT)) {
               term = tb.gt(term.sub(0), subOne.sub(1));
            }
            else if (isOne(subOne.sub(1), integerLDT)) {
               term = tb.gt(term.sub(0), subOne.sub(0));
            }
         }
      }
      // Improve readability: a <= -1 + b, a <= 1 + -b, a <= 1 - b
      else if (term.op() == integerLDT.getLessOrEquals()) {
         Term subOne = term.sub(1);
         if (subOne.op() == integerLDT.getAdd()) {
            if (isMinusOne(subOne.sub(0), integerLDT)) {
               term = tb.lt(term.sub(0), subOne.sub(1));
            }
            else if (isMinusOne(subOne.sub(1), integerLDT)) {
               term = tb.lt(term.sub(0), subOne.sub(0));
            }
         }
         else if (subOne.op() == integerLDT.getSub()) {
            if (isOne(subOne.sub(1), integerLDT)) {
               term = tb.lt(term.sub(0), subOne.sub(0));
            }
         }
      }
      // Improve readability: a > -1 + b, a > 1 + -b, a > 1 - b
      else if (term.op() == integerLDT.getGreaterThan()) {
         Term subOne = term.sub(1);
         if (subOne.op() == integerLDT.getAdd()) {
            if (isMinusOne(subOne.sub(0), integerLDT)) {
               term = tb.geq(term.sub(0), subOne.sub(1));
            }
            else if (isMinusOne(subOne.sub(1), integerLDT)) {
               term = tb.geq(term.sub(0), subOne.sub(0));
            }
         }
         else if (subOne.op() == integerLDT.getSub()) {
            if (isOne(subOne.sub(1), integerLDT)) {
               term = tb.geq(term.sub(0), subOne.sub(0));
            }
         }
      }
      // Improve readability: !a >= b, !a > b, !a <= b, !a < b
      else if (term.op() == Junctor.NOT) {
         Term sub = term.sub(0);
         if (sub.op() == integerLDT.getLessOrEquals()) {
            term = tb.gt(sub.sub(0), sub.sub(1));
         }
         else if (sub.op() == integerLDT.getLessThan()) {
            term = tb.geq(sub.sub(0), sub.sub(1));
         }
         else if (sub.op() == integerLDT.getGreaterOrEquals()) {
            term = tb.lt(sub.sub(0), sub.sub(1));
         }
         else if (sub.op() == integerLDT.getGreaterThan()) {
            term = tb.leq(sub.sub(0), sub.sub(1));
         }
      }
      return term;
   }

   /**
    * Checks if the given term represent the number one
    * @param subOne the term to be checked
    * @param integerLDT the LDT for integers
    * @return true if the term represents the one
    */
   private static boolean isOne(Term subOne, IntegerLDT integerLDT) {
       return subOne.equals(integerLDT.one());
   }

   /**
    * Checks if the given {@link Term} represents the integer constant {@code -1}.
    * @param term The {@link Term} to check.
    * @param integerLDT The {@link IntegerLDT} to use.
    * @return {@code true} {@link Term} represents {@code -1}, {@code false} {@link Term} is something else.
    */
   private static boolean isMinusOne(Term term, IntegerLDT integerLDT) {
      if (term.op() == integerLDT.getNumberSymbol()) {
         term = term.sub(0);
         if (term.op() == integerLDT.getNegativeNumberSign()) {
            term = term.sub(0);
            if (term.op() == integerLDT.getNumberLiteralFor(1)) {
               term = term.sub(0);
               if (term.op() == integerLDT.getNumberTerminator()) {
                  return true;
               }
            }
         }
      }
      return false;
   }
   
   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the return value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param services The {@link Services} to use.
    * @param contextObjectType The type of the current object (this reference).
    * @param contextMethod The current method.
    * @param contextObject The current object (this reference).
    * @param methodReturnNode The method return {@link Node} which provides the sequent to extract updates and return expression from.
    * @param methodCallEmptyNode The method call empty {@link Node} which provides the sequent to start site proof in.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   public static SiteProofVariableValueInput createExtractReturnVariableValueSequent(Services services,
                                                                                     TypeReference contextObjectType,
                                                                                     IProgramMethod contextMethod,
                                                                                     ReferencePrefix contextObject,
                                                                                     Node methodReturnNode,
                                                                                     Node methodCallEmptyNode,
                                                                                     IProgramVariable variable) {
      // Create execution context in that the method was called.
      IExecutionContext context = new ExecutionContext(contextObjectType, contextMethod, contextObject);
      // Create sequent
      return createExtractReturnVariableValueSequent(services, context, methodReturnNode, methodCallEmptyNode, variable);
   }

   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the return value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param services The {@link Services} to use.
    * @param context The {@link IExecutionContext} that defines the current object (this reference).
    * @param methodReturnNode The method return {@link Node} which provides the sequent to extract updates and return expression from.
    * @param methodCallEmptyNode The method call empty {@link Node} which provides the sequent to start site proof in.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   public static SiteProofVariableValueInput createExtractReturnVariableValueSequent(Services services,
                                                                                     IExecutionContext context,
                                                                                     Node methodReturnNode,
                                                                                     Node methodCallEmptyNode,
                                                                                     IProgramVariable variable) {
      // Make sure that correct parameters are given
      assert context != null;
      assert methodReturnNode != null;
      assert methodCallEmptyNode != null;
      assert variable instanceof ProgramVariable;
      // Create method frame which will be executed in site proof
      Statement originalReturnStatement = (Statement)methodReturnNode.getNodeInfo().getActiveStatement();
      MethodFrame newMethodFrame = new MethodFrame(variable, context, new StatementBlock(originalReturnStatement));
      JavaBlock newJavaBlock = JavaBlock.createJavaBlock(new StatementBlock(newMethodFrame));
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(services.getTermBuilder().newName("ResultPredicate")), Sort.FORMULA, variable.sort());
      // Create formula which contains the value interested in.
      Term newTerm = services.getTermBuilder().func(newPredicate, services.getTermBuilder().var((ProgramVariable)variable));
      // Combine method frame with value formula in a modality.
      Term modalityTerm = services.getTermBuilder().dia(newJavaBlock, newTerm);
      // Get the updates from the return node which includes the value interested in.
      Term originalModifiedFormula = methodReturnNode.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
      ImmutableList<Term> originalUpdates = TermBuilder.goBelowUpdates2(originalModifiedFormula).first;
      // Create Sequent to prove with new succedent.
      Sequent sequentToProve = createSequentToProveWithNewSuccedent(methodCallEmptyNode, null, modalityTerm, originalUpdates, false);
      // Return created sequent and the used predicate to identify the value interested in.
      return new SiteProofVariableValueInput(sequentToProve, newPredicate);
   }

   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param services The {@link Services} to use.
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param pio The {@link PosInOccurrence} of the SE modality.
    * @param additionalConditions Optional additional conditions.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   public static SiteProofVariableValueInput createExtractVariableValueSequent(Services services,
                                                                               Node node,
                                                                               PosInOccurrence pio,
                                                                               Term additionalConditions,
                                                                               IProgramVariable variable) {
      // Make sure that correct parameters are given
      assert node != null;
      assert variable instanceof ProgramVariable;
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(services.getTermBuilder().newName("ResultPredicate")), Sort.FORMULA, variable.sort());
      // Create formula which contains the value interested in.
      Term newTerm = services.getTermBuilder().func(newPredicate, services.getTermBuilder().var((ProgramVariable)variable));
      // Create Sequent to prove with new succedent.
      Sequent sequentToProve = createSequentToProveWithNewSuccedent(node, pio, additionalConditions, newTerm, false);
      // Return created sequent and the used predicate to identify the value interested in.
      return new SiteProofVariableValueInput(sequentToProve, newPredicate);
   }

   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param sideProofServices The {@link Services} of the side proof to use.
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param pio The {@link PosInOccurrence} of the modality or its updates.
    * @param additionalConditions Additional conditions to add to the antecedent.
    * @param term The new succedent term.
    * @param keepUpdates {@code true} keep updates, {@code false} throw updates away.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   public static SiteProofVariableValueInput createExtractTermSequent(Services sideProofServices,
                                                                      Node node,
                                                                      PosInOccurrence pio,
                                                                      Term additionalConditions,
                                                                      Term term,
                                                                      boolean keepUpdates) {
      // Make sure that correct parameters are given
      assert node != null;
      assert term != null;
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(sideProofServices.getTermBuilder().newName("ResultPredicate")), Sort.FORMULA, term.sort());
      // Create formula which contains the value interested in.
      Term newTerm = sideProofServices.getTermBuilder().func(newPredicate, term);
      // Create Sequent to prove with new succedent.
      Sequent sequentToProve = keepUpdates ? 
                               createSequentToProveWithNewSuccedent(node, pio, additionalConditions, newTerm, false) :
                               createSequentToProveWithNewSuccedent(node, pio, additionalConditions, newTerm, null, false);
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
    * Checks if it is right now possible to compute the variables of the given {@link IExecutionNode}
    * via {@link IExecutionNode#getVariables()}. 
    * @param node The {@link IExecutionNode} to check.
    * @param services The {@link Services} to use.
    * @return {@code true} right now it is possible to compute variables, {@code false} it is not possible to compute variables.
    * @throws ProofInputException Occurred Exception.
    */
   public static boolean canComputeVariables(IExecutionNode<?> node, Services services) throws ProofInputException {
      return node != null && 
             !node.isDisposed() &&
             !services.getTermBuilder().ff().equals(node.getPathCondition());
   }

   /**
    * Creates for the given {@link IExecutionNode} the contained
    * {@link IExecutionConstraint}s.
    * @param node The {@link IExecutionNode} to create constraints for.
    * @return The created {@link IExecutionConstraint}s.
    */
   public static IExecutionConstraint[] createExecutionConstraints(IExecutionNode<?> node) {
      if (node != null && !node.isDisposed()) {
         TermBuilder tb = node.getServices().getTermBuilder();
         List<IExecutionConstraint> constraints = new LinkedList<IExecutionConstraint>();
         Node proofNode = node.getProofNode();
         Sequent sequent = proofNode.sequent();
         for (SequentFormula sf : sequent.antecedent()) {
            if (!containsSymbolicExecutionLabel(sf.formula())) {
               constraints.add(new ExecutionConstraint(node.getSettings(), proofNode, node.getModalityPIO(), sf.formula()));
            }
         }
         for (SequentFormula sf : sequent.succedent()) {
            if (!containsSymbolicExecutionLabel(sf.formula())) {
               constraints.add(new ExecutionConstraint(node.getSettings(), proofNode, node.getModalityPIO(), tb.not(sf.formula())));
            }
         }
         return constraints.toArray(new IExecutionConstraint[constraints.size()]);
      }
      else {
         return new IExecutionConstraint[0];
      }
   }
   
   /**
    * Checks if the {@link Term} or one of its sub terms contains
    * a symbolic execution label.
    * @param term The {@link Term} to check.
    * @return {@code true} SE label is somewhere contained, {@code false} SE label is not contained at all.
    */
   public static boolean containsSymbolicExecutionLabel(Term term) {
      boolean hasModality = false;
      term = TermBuilder.goBelowUpdates(term);
      if (term.op() instanceof Modality) {
         hasModality = hasSymbolicExecutionLabel(term);
      }
      if (!hasModality) {
         int i = 0;
         while (!hasModality && i < term.arity()) {
            hasModality = containsSymbolicExecutionLabel(term.sub(i));
            i++;
         }
      }
      return hasModality;
   }

   /**
    * Creates for the given {@link IExecutionNode} the contained
    * root {@link IExecutionVariable}s.
    * @param node The {@link IExecutionNode} to create variables for.
    * @return The created {@link IExecutionVariable}s.
    * @throws ProofInputException 
    */
   public static IExecutionVariable[] createExecutionVariables(IExecutionNode<?> node) throws ProofInputException {
      return createExecutionVariables(node, null);
   }

   /**
    * Creates for the given {@link IExecutionNode} the contained
    * root {@link IExecutionVariable}s.
    * @param node The {@link IExecutionNode} to create variables for.
    * @param condition A {@link Term} specifying some additional constraints to consider.
    * @return The created {@link IExecutionVariable}s.
    * @throws ProofInputException 
    */
   public static IExecutionVariable[] createExecutionVariables(IExecutionNode<?> node, Term condition) throws ProofInputException {
      if (node != null) {
         return createExecutionVariables(node, node.getProofNode(), node.getModalityPIO(), condition);
      }
      else {
         return new IExecutionVariable[0];
      }
   }

   /**
    * Creates for the given {@link IExecutionNode} the contained
    * root {@link IExecutionVariable}s.
    * @param node The {@link IExecutionNode} to create variables for.
    * @param proofNode The proof {@link Node} to work with.
    * @param modalityPIO The {@link PosInOccurrence} of the modality of interest.
    * @param condition A {@link Term} specifying some additional constraints to consider.
    * @return The created {@link IExecutionVariable}s.
    * @throws ProofInputException 
    */
   public static IExecutionVariable[] createExecutionVariables(IExecutionNode<?> node, 
                                                               Node proofNode, 
                                                               PosInOccurrence modalityPIO, 
                                                               Term condition) throws ProofInputException {
      if (node.getSettings().isVariablesAreOnlyComputedFromUpdates()) {
         ExecutionVariableExtractor extractor = new ExecutionVariableExtractor(proofNode, modalityPIO, node, condition);
         return extractor.analyse();
      }
      else {
         return createAllExecutionVariables(node, proofNode, modalityPIO, condition);
      }
   }

   /**
    * Creates for the given {@link IExecutionNode} the contained
    * root {@link IExecutionVariable}s.
    * @param node The {@link IExecutionNode} to create variables for.
    * @param proofNode The proof {@link Node} to work with.
    * @param modalityPIO The {@link PosInOccurrence} of the modality of interest.
    * @param condition A {@link Term} specifying some additional constraints to consider.
    * @return The created {@link IExecutionVariable}s.
    */
   public static IExecutionVariable[] createAllExecutionVariables(IExecutionNode<?> node, 
                                                                  Node proofNode, 
                                                                  PosInOccurrence modalityPIO, 
                                                                  Term condition) {
      if (proofNode != null) {
         List<IProgramVariable> variables = new LinkedList<IProgramVariable>();
         // Add self variable
         IProgramVariable selfVar = findSelfTerm(proofNode, modalityPIO);
         if (selfVar != null) {
            variables.add(selfVar);
         }
         // Add method parameters
         Node callNode = findMethodCallNode(proofNode, modalityPIO);
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
            result[i] = new ExecutionVariable(node, proofNode, modalityPIO, var, condition);
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
   private static void internalCollectAllElementaryUpdateTerms(Services services,
                                                               List<IProgramVariable> result,
                                                               Term term) {
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
   private static void internalCollectStaticProgramVariablesOnHeap(Services services,
                                                                   Set<IProgramVariable> result,
                                                                   Term term) {
      final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
      try {
         if (term.op() == heapLDT.getStore()) {
            ImmutableArray<Term> subs = term.subs();
            if (term.arity() == 4) {
               Term innerMostSelect = findInnerMostSelect(subs.get(1), services);
               Term locationTerm = innerMostSelect != null ? innerMostSelect.sub(2) : subs.get(2);
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
   
   private static Term findInnerMostSelect(Term term, Services services) {
      if (isSelect(services, term)) {
         while (isSelect(services, term.sub(1))) {
            term = term.sub(1);
         }
         return term;
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the {@link ProgramVariable} defined by the given {@link Term}.
    * @param services The {@link Services} to use.
    * @param heapLDT The {@link HeapLDT} to use.
    * @param locationTerm The {@link Term} to extract {@link ProgramVariable} from.
    * @return The {@link Term}s {@link ProgramVariable} or {@code null} if not available.
    */
   public static ProgramVariable getProgramVariable(Services services, HeapLDT heapLDT,
                                                    Term locationTerm) {
      ProgramVariable result = null;
      if (locationTerm.op() instanceof Function) {
         Function function = (Function)locationTerm.op();
         // Make sure that the function is not an array
         if (heapLDT.getArr() != function) {
            String typeName = HeapLDT.getClassName(function);
            KeYJavaType type = services.getJavaInfo().getKeYJavaType(typeName);
            if (type != null) {
               String fieldName = HeapLDT.getPrettyFieldName(function);
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
    * @return The array index or {@code null} if the term defines no array index.
    */
   public static Term getArrayIndex(Services services, HeapLDT heapLDT, Term arrayIndexTerm) {
      // Make sure that the term is an array index
      if (arrayIndexTerm.op() == heapLDT.getArr() && arrayIndexTerm.arity() == 1) {
         return arrayIndexTerm.sub(0);
      }
      else {
         return null;
      }
   }

   /**
    * Searches the {@link IProgramVariable} of the current {@code this}/{@code self} reference.
    * @param node The {@link Node} to search in.
    * @param pio The {@link PosInOccurrence} describing the location of the modality of interest.
    * @return The found {@link IProgramVariable} with the current {@code this}/{@code self} reference or {@code null} if no one is available.
    */
   public static IProgramVariable findSelfTerm(Node node, PosInOccurrence pio) {
      if (pio != null) {
         Term term = pio.subTerm();
         term = TermBuilder.goBelowUpdates(term);
         JavaBlock jb = term.javaBlock();
         Services services = node.proof().getServices();
         IExecutionContext context = JavaTools.getInnermostExecutionContext(jb, services);
         if (context instanceof ExecutionContext) {
            ReferencePrefix prefix = context.getRuntimeInstance();
            return prefix instanceof IProgramVariable ? (IProgramVariable)prefix : null;
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
   public static boolean isMethodCallNode(Node node, RuleApp ruleApp,
                                          SourceElement statement, boolean allowImpliciteMethods) {
      if (ruleApp != null) { // Do not handle open goal nodes without applied rule
         if (statement instanceof MethodBodyStatement) {
            if (allowImpliciteMethods) {
               return true;
            }
            else {
               MethodBodyStatement mbs = (MethodBodyStatement)statement;
               IProgramMethod pm = mbs.getProgramMethod(node.proof().getServices());
               return isNotImplicit(node.proof().getServices(), pm);
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
    * Checks if the given {@link IProgramMethod} is not implicit.
    * @param services The {@link Services} to use.
    * @param pm The {@link IProgramMethod} to check.
    * @return {@code true} is not implicit, {@code false} is implicit 
    */
   public static boolean isNotImplicit(Services services, IProgramMethod pm) {
      if (pm != null) {
         if (KeYTypeUtil.isImplicitConstructor(pm)) {
            IProgramMethod explicitConstructor = KeYTypeUtil.findExplicitConstructor(services, pm);
            return explicitConstructor != null && 
                   !KeYTypeUtil.isLibraryClass(explicitConstructor.getContainerType());
         }
         else {
            return !pm.isImplicit() && // Do not include implicit methods, but always constructors
                   !KeYTypeUtil.isLibraryClass(pm.getContainerType());
         }
      }
      else {
         return true;
      }
   }
   
   /**
    * Checks if the given node should be represented as branch statement.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @param statement The statement ({@link SourceElement}).
    * @param posInfo The {@link PositionInfo}.
    * @return {@code true} represent node as branch statement, {@code false} represent node as something else. 
    */
   public static boolean isBranchStatement(Node node, RuleApp ruleApp,
                                           SourceElement statement, PositionInfo posInfo) {
      return isStatementNode(node, ruleApp, statement, posInfo) &&
             (statement instanceof BranchStatement); 
   }
   
   /**
    * Checks if the given node should be represented as loop statement.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @param statement The statement ({@link SourceElement}).
    * @param posInfo The {@link PositionInfo}.
    * @return {@code true} represent node as loop statement, {@code false} represent node as something else. 
    */
   public static boolean isLoopStatement(Node node, RuleApp ruleApp,
                                         SourceElement statement, PositionInfo posInfo) {
      return isStatementNode(node, ruleApp, statement, posInfo) &&
             (statement instanceof LoopStatement);
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
             !(statement instanceof StatementBlock && ((StatementBlock)statement).isEmpty()); // Filter out empty blocks
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
    * Checks if the given node should be represented as operation contract.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} represent node as operation contract, {@code false} represent node as something else. 
    */
   public static boolean isOperationContract(Node node, RuleApp ruleApp) {
      if (ruleApp instanceof AbstractContractRuleApp) {
         Contract contract = ((AbstractContractRuleApp)ruleApp).getInstantiation();
         if (contract instanceof OperationContract) {
            IProgramMethod target = ((OperationContract)contract).getTarget();
            return isNotImplicit(node.proof().getServices(), target);
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
    * Checks if the given node should be represented as loop invariant.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} represent node as use loop invariant, {@code false} represent node as something else. 
    */
   public static boolean isLoopInvariant(Node node, RuleApp ruleApp) {
      return "Loop Invariant".equals(MiscTools.getRuleDisplayName(ruleApp));
   }
   
   /**
    * Checks if the given node should be represented as method return.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} represent node as method return, {@code false} represent node as something else. 
    */
   public static boolean isMethodReturnNode(Node node, RuleApp ruleApp) {
      String displayName = MiscTools.getRuleDisplayName(ruleApp);
      String ruleName = MiscTools.getRuleName(ruleApp);
      return "methodCallEmpty".equals(displayName) ||
             "methodCallEmptyReturn".equals(ruleName) ||
             "methodCallReturnIgnoreResult".equals(ruleName);
   }
   
   /**
    * Checks if the given node should be represented as exceptional method return.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} represent node as exceptional method return, {@code false} represent node as something else. 
    */
   public static boolean isExceptionalMethodReturnNode(Node node, RuleApp ruleApp) {
      String ruleName = MiscTools.getRuleName(ruleApp);
      return "methodCallParamThrow".equals(ruleName) || "methodCallThrow".equals(ruleName);
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
    * Checks if the {@link Term} on which the {@link RuleApp} was applied contains a {@link SymbolicExecutionTermLabel}.
    * @param ruleApp The {@link RuleApp} to check.
    * @return {@code true} contains a {@link SymbolicExecutionTermLabel}, {@code false} does not contain a {@link SymbolicExecutionTermLabel} or the given {@link RuleApp} is {@code null}.
    */
   public static boolean hasLoopBodyLabel(RuleApp ruleApp) {
      if (ruleApp != null && ruleApp.posInOccurrence() != null) {
         Term term = ruleApp.posInOccurrence().subTerm();
         if (term != null) {
            term = TermBuilder.goBelowUpdates(term);
            return term.containsLabel(LOOP_BODY_LABEL);
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
    * Checks if the {@link Term} on which the {@link RuleApp} was applied contains a {@link SymbolicExecutionTermLabel}.
    * @param ruleApp The {@link RuleApp} to check.
    * @return {@code true} contains a {@link SymbolicExecutionTermLabel}, {@code false} does not contain a {@link SymbolicExecutionTermLabel} or the given {@link RuleApp} is {@code null}.
    */
   public static boolean hasLoopBodyTerminationLabel(RuleApp ruleApp) {
      if (ruleApp != null && ruleApp.posInOccurrence() != null) {
         Term term = ruleApp.posInOccurrence().subTerm();
         return term.containsLabel(LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL);
      }
      else {
         return false;
      }
   }
   
   /**
    * Checks if the {@link Term} on which the {@link RuleApp} was applied contains a {@link SymbolicExecutionTermLabel}.
    * @param ruleApp The {@link RuleApp} to check.
    * @return {@code true} contains a {@link SymbolicExecutionTermLabel}, {@code false} does not contain a {@link SymbolicExecutionTermLabel} or the given {@link RuleApp} is {@code null}.
    */
   public static boolean hasSymbolicExecutionLabel(RuleApp ruleApp) {
      return getSymbolicExecutionLabel(ruleApp) != null;
   }
   
   /**
    * Returns the contained {@link SymbolicExecutionTermLabel} if available.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return The first found {@link SymbolicExecutionTermLabel} or {@code null} if no {@link SymbolicExecutionTermLabel} is provided.
    */
   public static SymbolicExecutionTermLabel getSymbolicExecutionLabel(RuleApp ruleApp) {
      if (ruleApp != null && ruleApp.posInOccurrence() != null) {
         return getSymbolicExecutionLabel(ruleApp.posInOccurrence().subTerm());
      }
      else {
         return null;
      }
   }
   
   /**
    * Checks if the given {@link Term} contains a {@link SymbolicExecutionTermLabel}.
    * @param term The {@link Term} to check.
    * @return {@code true} contains a {@link SymbolicExecutionTermLabel}, {@code false} does not contain a {@link SymbolicExecutionTermLabel} or the given {@link Term} is {@code null}.
    */
   public static boolean hasSymbolicExecutionLabel(Term term) {
      return getSymbolicExecutionLabel(term) != null;
   }
   
   /**
    * Returns the contained {@link SymbolicExecutionTermLabel} if available.
    * @param term The {@link Term} to search in.
    * @return The first found {@link SymbolicExecutionTermLabel} or {@code null} if no {@link SymbolicExecutionTermLabel} is provided.
    */
   public static SymbolicExecutionTermLabel getSymbolicExecutionLabel(Term term) {
      if (term != null) {
         term = TermBuilder.goBelowUpdates(term);
         return (SymbolicExecutionTermLabel)CollectionUtil.search(term.getLabels(),
                                                            new IFilter<TermLabel>() {
            @Override
            public boolean select(TermLabel element) {
               return element instanceof SymbolicExecutionTermLabel;
            }
         });
      }
      else {
         return null;
      }
   }
   
   /**
    * Searches the modality {@link PosInOccurrence} with the maximal {@link SymbolicExecutionTermLabel} ID
    * {@link SymbolicExecutionTermLabel#getId()} in the given {@link Sequent}.
    * @param sequent The {@link Sequent} to search in.
    * @return The modality {@link PosInOccurrence} with the maximal ID if available or {@code null} otherwise.
    */
   public static PosInOccurrence findModalityWithMaxSymbolicExecutionLabelId(Sequent sequent) {
      if (sequent != null) {
         PosInOccurrence nextAntecedent = findModalityWithMaxSymbolicExecutionLabelId(sequent.antecedent(), true);
         PosInOccurrence nextSuccedent = findModalityWithMaxSymbolicExecutionLabelId(sequent.succedent(), false);
         if (nextAntecedent != null) {
            if (nextSuccedent != null) {
               SymbolicExecutionTermLabel antecedentLabel = getSymbolicExecutionLabel(nextAntecedent.subTerm());
               SymbolicExecutionTermLabel succedentLabel = getSymbolicExecutionLabel(nextSuccedent.subTerm());
               return antecedentLabel.getId() > succedentLabel.getId() ?
                       nextAntecedent : nextSuccedent;
            }
            else {
               return nextAntecedent;
            }
         }
         else {
            return nextSuccedent;
         }
      }
      else {
         return null;
      }
   }

   /**
    * Searches the modality {@link Term} with the maximal {@link SymbolicExecutionTermLabel} ID
    * {@link SymbolicExecutionTermLabel#getId()} in the given {@link Semisequent}.
    * @param semisequent The {@link Semisequent} to search in.
    * @param inAntec {@code true} antecedent, {@code false} succedent.
    * @return The modality {@link Term} with the maximal ID if available or {@code null} otherwise.
    */
   public static PosInOccurrence findModalityWithMaxSymbolicExecutionLabelId(Semisequent semisequent, boolean inAntec) {
      if (semisequent != null) {
         int maxId = Integer.MIN_VALUE;
         PosInOccurrence maxPio = null;
         for (SequentFormula sf : semisequent) {
            PosInTerm current = findModalityWithMaxSymbolicExecutionLabelId(sf.formula());
            if (current != null) {
               PosInOccurrence pio = new PosInOccurrence(sf, current, inAntec);
               SymbolicExecutionTermLabel label = getSymbolicExecutionLabel(pio.subTerm());
               if (maxPio == null || label.getId() > maxId) {
                  maxPio = pio;
                  maxId = label.getId();
               }
            }
         }
         return maxPio;
      }
      else {
         return null;
      }
   }

   /**
    * Searches the modality {@link PosInTerm} with the maximal {@link SymbolicExecutionTermLabel} ID
    * {@link SymbolicExecutionTermLabel#getId()} in the given {@link Term}.
    * @param term The {@link Term} to search in.
    * @return The modality {@link PosInTerm} with the maximal ID if available or {@code null} otherwise.
    */
   public static PosInTerm findModalityWithMaxSymbolicExecutionLabelId(Term term) {
      if (term != null) {
         FindModalityWithSymbolicExecutionLabelId visitor = new FindModalityWithSymbolicExecutionLabelId(true);
         term.execPreOrder(visitor);
         return visitor.getPosInTerm();
      }
      else {
         return null;
      }
   }
   
   /**
    * Searches the modality {@link PosInOccurrence} with the minimal {@link SymbolicExecutionTermLabel} ID
    * {@link SymbolicExecutionTermLabel#getId()} in the given {@link Sequent}.
    * @param sequent The {@link Sequent} to search in.
    * @return The modality {@link PosInOccurrence} with the maximal ID if available or {@code null} otherwise.
    */
   public static PosInOccurrence findModalityWithMinSymbolicExecutionLabelId(Sequent sequent) {
      if (sequent != null) {
         PosInOccurrence nextAntecedent = findModalityWithMinSymbolicExecutionLabelId(sequent.antecedent(), true);
         PosInOccurrence nextSuccedent = findModalityWithMinSymbolicExecutionLabelId(sequent.succedent(), false);
         if (nextAntecedent != null) {
            if (nextSuccedent != null) {
               SymbolicExecutionTermLabel antecedentLabel = getSymbolicExecutionLabel(nextAntecedent.subTerm());
               SymbolicExecutionTermLabel succedentLabel = getSymbolicExecutionLabel(nextSuccedent.subTerm());
               return antecedentLabel.getId() < succedentLabel.getId() ? nextAntecedent : nextSuccedent;
            }
            else {
               return nextAntecedent;
            }
         }
         else {
            return nextSuccedent;
         }
      }
      else {
         return null;
      }
   }

   /**
    * Searches the modality {@link PosInOccurrence} with the minimal {@link SymbolicExecutionTermLabel} ID
    * {@link SymbolicExecutionTermLabel#getId()} in the given {@link Semisequent}.
    * @param semisequent The {@link Semisequent} to search in.
    * @param inAntec {@code true} antecedent, {@code false} succedent.
    * @return The modality {@link PosInOccurrence} with the minimal ID if available or {@code null} otherwise.
    */
   public static PosInOccurrence findModalityWithMinSymbolicExecutionLabelId(Semisequent semisequent, boolean inAntec) {
      if (semisequent != null) {
         int maxId = Integer.MIN_VALUE;
         PosInOccurrence minPio = null;
         for (SequentFormula sf : semisequent) {
            PosInTerm current = findModalityWithMinSymbolicExecutionLabelId(sf.formula());
            if (current != null) {
               PosInOccurrence pio = new PosInOccurrence(sf, current, inAntec);
               SymbolicExecutionTermLabel label = getSymbolicExecutionLabel(pio.subTerm());
               if (minPio == null || label.getId() < maxId) {
                  minPio = pio;
                  maxId = label.getId();
               }
            }
         }
         return minPio;
      }
      else {
         return null;
      }
   }

   /**
    * Searches the modality {@link PosInTerm} with the minimal {@link SymbolicExecutionTermLabel} ID
    * {@link SymbolicExecutionTermLabel#getId()} in the given {@link Term}.
    * @param term The {@link Term} to search in.
    * @return The modality {@link PosInTerm} with the maximal ID if available or {@code null} otherwise.
    */
   public static PosInTerm findModalityWithMinSymbolicExecutionLabelId(Term term) {
      if (term != null) {
         FindModalityWithSymbolicExecutionLabelId visitor = new FindModalityWithSymbolicExecutionLabelId(false);
         term.execPreOrder(visitor);
         return visitor.getPosInTerm();
      }
      else {
         return null;
      }
   }
   
   /**
    * Utility class used to find the maximal modality Term
    * used by {@link SymbolicExecutionUtil#findModalityWithMaxSymbolicExecutionLabelId(Term)}.
    * @author Martin Hentschel
    */
   private static final class FindModalityWithSymbolicExecutionLabelId extends DefaultVisitor {
      /**
       * The modality {@link PosInTerm} with the maximal ID.
       */
      private PosInTerm posInTerm;
      
      /**
       * The maximal ID.
       */
      private int maxId;
      
      /**
       * {@code true} search maximal ID, {@code false} search minimal ID.
       */
      private boolean maximum;
      
      /**
       * The current {@link PosInTerm}.
       */
      private PosInTerm currentPosInTerm = null;
      
      private Deque<Integer> indexStack = new LinkedList<Integer>();
      
      /**
       * Constructor.
       * @param maximum {@code true} search maximal ID, {@code false} search minimal ID.
       */
      public FindModalityWithSymbolicExecutionLabelId(boolean maximum) {
         this.maximum = maximum;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void visit(Term visited) {
         SymbolicExecutionTermLabel label = getSymbolicExecutionLabel(visited);
         if (label != null) {
            if (posInTerm == null || (maximum ? label.getId() > maxId : label.getId() < maxId)) {
               posInTerm = currentPosInTerm;
               maxId = label.getId();
            }
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void subtreeEntered(Term subtreeRoot) {
         if (currentPosInTerm == null) {
            currentPosInTerm = PosInTerm.getTopLevel();
         }
         else {
            int index = indexStack.getFirst();
            currentPosInTerm = currentPosInTerm.down(index);
         }
         indexStack.addFirst(0);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void subtreeLeft(Term subtreeRoot) {
         currentPosInTerm = currentPosInTerm.up();
         indexStack.removeFirst();
         if (!indexStack.isEmpty()) {
            Integer nextIndex = indexStack.removeFirst();
            indexStack.addFirst(nextIndex + 1);
         }
      }

      /**
       * Returns the modality {@link PosInTerm} with the maximal ID.
       * @return The modality {@link PosInTerm} with the maximal ID.
       */
      public PosInTerm getPosInTerm() {
         return posInTerm;
      }
   }

   /**
    * Checks if the given {@link Node} in KeY's proof tree represents
    * also a {@link Node} in a symbolic execution tree.
    * @param node The {@link Node} of KeY's proof tree to check.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} is also symbolic execution tree node, {@code false} is no node in a symbolic execution tree.
    */
   public static boolean isSymbolicExecutionTreeNode(Node node, RuleApp ruleApp) {
      if (node != null && !isRuleAppToIgnore(ruleApp) && hasSymbolicExecutionLabel(ruleApp)) {
         SourceElement statement = NodeInfo.computeActiveStatement(ruleApp);
         PositionInfo posInfo = statement != null ? statement.getPositionInfo() : null;
         if (isMethodReturnNode(node, ruleApp)) {
            return !isInImplicitMethod(node, ruleApp);
         }
         else if (isExceptionalMethodReturnNode(node, ruleApp)) {
            return !isInImplicitMethod(node, ruleApp);
         }
         else if (isLoopStatement(node, ruleApp, statement, posInfo)) { // This check is redundant to the loop iteration check, but is faster
            return true;
         }
         else if (isBranchStatement(node, ruleApp, statement, posInfo) ||
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
         else if (isOperationContract(node, ruleApp)) {
            return true;
         }
         else if (isLoopInvariant(node, ruleApp)) {
            return true;
         }
         else {
            return false;
         }
      }
      else if (isLoopBodyTermination(node, ruleApp)) {
         return true;
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
      Term term = ruleApp.posInOccurrence().subTerm();
      term = TermBuilder.goBelowUpdates(term);
      JavaBlock block = term.javaBlock();
      IExecutionContext context =
              JavaTools.getInnermostExecutionContext(block, node.proof().getServices());
      return context != null && context.getMethodContext() != null
              && context.getMethodContext().isImplicit();
   }
   
   /**
    * Compute the stack size of the given {@link Term} described by the given {@link RuleApp}.
    * @param ruleApp The {@link RuleApp} which defines the {@link Term} to compute its stack size.
    * @return The stack size.
    */
   public static int computeStackSize(RuleApp ruleApp) {
      int result = 0;
      if (ruleApp != null) {
         PosInOccurrence posInOc = ruleApp.posInOccurrence();
         if (posInOc != null) {
            Term subTerm = posInOc.subTerm();
            if (subTerm != null) {
               Term modality = TermBuilder.goBelowUpdates(subTerm);
               if (modality != null) {
                  JavaBlock block = modality.javaBlock();
                  if (block != null) {
                     JavaProgramElement element = block.program();
                     if (element instanceof StatementBlock) {
                        StatementBlock b = (StatementBlock)block.program();
                        ImmutableArray<ProgramPrefix> prefix = b.getPrefixElements();
                        result = CollectionUtil.count(prefix, new IFilter<ProgramPrefix>() {
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
         Iterator<Node> iter = node.leavesIterator();
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
    * @param pio The {@link PosInOccurrence} of the modality.
    * @return The parent {@link Node} of the given {@link Node} which is also a set node or {@code null} if no parent node was found.
    */
   public static Node findMethodCallNode(Node node, PosInOccurrence pio) {
      if (node != null && pio != null) {
         // Get current program method
         Term term = pio.subTerm();
         term = TermBuilder.goBelowUpdates(term);
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
    * @param simplify {@code true} simplify condition in a side proof, {@code false} do not simplify condition.
    * @param improveReadability {@code true} improve readability, {@code false} do not improve readability.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term computeBranchCondition(Node node,
                                             boolean simplify,
                                             boolean improveReadability) throws ProofInputException {
      // Get applied taclet on parent proof node
      Node parent = node.parent();
      if (parent.getAppliedRuleApp() instanceof TacletApp) {
         return computeTacletAppBranchCondition(parent, node, simplify, improveReadability);
      }
      else if (parent.getAppliedRuleApp() instanceof ContractRuleApp) {
        return computeContractRuleAppBranchCondition(parent, node, simplify, improveReadability);
      }
      else if (parent.getAppliedRuleApp() instanceof LoopInvariantBuiltInRuleApp) {
         return computeLoopInvariantBuiltInRuleAppBranchCondition(parent, node, simplify, improveReadability);
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
    *    <li>Post:    caller != null & (pre1 | .. | preN)</li>
    *    <li>ExcPost: caller != null & (excPre1 | ... | excPreM)</li>
    *    <li>Pre:     caller != null & !(pre1 | ... | preN | excPre1 | ... | excPreM) because the branch is only open if all conditions are false</li>
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
    * @param simplify {@code true} simplify condition in a side proof, {@code false} do not simplify condition.
    * @param improveReadability {@code true} improve readability, {@code false} do not improve readability.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   private static Term computeContractRuleAppBranchCondition(Node parent,
                                                             Node node,
                                                             boolean simplify,
                                                             boolean improveReadability) throws ProofInputException {
      final Services services = node.proof().getServices();
      // Make sure that a computation is possible
      if (!(parent.getAppliedRuleApp() instanceof ContractRuleApp)) {
         throw new ProofInputException("Only ContractRuleApp is allowed in branch computation but rule \"" + parent.getAppliedRuleApp() + "\" was found.");
      }
      int childIndex = CollectionUtil.indexOf(parent.childrenIterator(), node);
      if (childIndex >= 3) {
         throw new ProofInputException("Branch condition of null pointer check is not supported.");
      }
      else if (childIndex == 2) {
         // Assumption: Original formula in parent is replaced
         PosInOccurrence pio = parent.getAppliedRuleApp().posInOccurrence();
         Term workingTerm = posInOccurrenceInOtherNode(parent, pio, node);
         if (workingTerm == null) {
            throw new ProofInputException("Term not find in precondition branch, implementation of UseOperationContractRule might have changed!");
         }
         workingTerm = TermBuilder.goBelowUpdates(workingTerm);
         if (workingTerm.op() != Junctor.AND) {
            throw new ProofInputException("And operation expected, implementation of UseOperationContractRule might have changed!");
         }
         Term preconditions = workingTerm.sub(0);
         return services.getTermBuilder().not(preconditions);
      }
      else {
         // Assumption: Pre -> Post & ExcPre -> Signals terms are added to last semisequent in antecedent.
         // Find Term to extract implications from.
         ContractPostOrExcPostExceptionVariableResult search = searchContractPostOrExcPostExceptionVariable(node, node.proof().getServices());
         
         List<Term> normalConditions = new LinkedList<Term>();
         List<Term> exceptinalConditions = new LinkedList<Term>();
         collectContractPreconditions(services, search, normalConditions, exceptinalConditions);
         List<Term> relevantConditions = childIndex == 1 ? // Exceptional case
                                         exceptinalConditions :
                                         normalConditions;
         Term result;
         if (relevantConditions.isEmpty()) {
            result = services.getTermBuilder().tt();
         }
         else {
            result = services.getTermBuilder().or(relevantConditions);
            // Add updates
            result = services.getTermBuilder().applyParallel(search.getUpdatesAndTerm().first, result);
         }
         // Add caller not null to condition
         if (parent.childrenCount() == 4) {
            Term callerNotNullTerm = posInOccurrenceInOtherNode(parent, parent.getAppliedRuleApp().posInOccurrence(), parent.child(3));
            callerNotNullTerm = TermBuilder.goBelowUpdates(callerNotNullTerm);
            if (callerNotNullTerm.op() != Junctor.NOT) {
               throw new ProofInputException("Not operation expected, implementation of UseOperationContractRule might have changed!");
            }
            if (callerNotNullTerm.sub(0).op() != Equality.EQUALS) {
               throw new ProofInputException("Equals operation expected, implementation of UseOperationContractRule might have changed!");
            }
            if (!(callerNotNullTerm.sub(0).sub(0).op() instanceof ProgramVariable)) {
               throw new ProofInputException("ProgramVariable expected, implementation of UseOperationContractRule might have changed!");
            }
            if (!isNullSort(callerNotNullTerm.sub(0).sub(1).sort(), parent.proof().getServices())) {
               throw new ProofInputException("Null expected, implementation of UseOperationContractRule might have changed!");
            }
            result = services.getTermBuilder().and(callerNotNullTerm, result);
         }
         // Create formula which contains the value interested in.
         Term condition;
         if (simplify) {
            final ProofEnvironment sideProofEnv = SymbolicExecutionSideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(parent.proof(), true); // New OneStepSimplifier is required because it has an internal state and the default instance can't be used parallel.
            Sequent newSequent = createSequentToProveWithNewSuccedent(parent, (Term)null, result, true);
            condition = evaluateInSideProof(services, 
                                            parent.proof(), 
                                            sideProofEnv,
                                            newSequent, 
                                            RESULT_LABEL, 
                                            "Operation contract branch condition computation on node " + parent.serialNr() + " for branch " + node.serialNr() + ".",
                                            StrategyProperties.SPLITTING_OFF);
         }
         else {
            condition = result;
         }
         if (improveReadability) {
            condition = improveReadability(condition, services);
         }
         return condition;
      }
   }
   
   /**
    * Collects the preconditions of an applied operation contract.
    * @param services The {@link Services} to use.
    * @param search The {@link ContractPostOrExcPostExceptionVariableResult}.
    * @param normalConditions The {@link List} with the normal case conditions to fill.
    * @param exceptinalConditions The {@link List} with the exceptional case conditions to fill.
    * @throws ProofInputException Occurred Exception.
    */
   private static void collectContractPreconditions(Services services, 
                                                    ContractPostOrExcPostExceptionVariableResult search,
                                                    List<Term> normalConditions,
                                                    List<Term> exceptinalConditions) throws ProofInputException {
      // Treat general conditions
      if (search.getWorkingTerm().op() != Junctor.AND) {
         throw new ProofInputException("And operation expected, implementation of UseOperationContractRule might has changed!"); 
      }
      Term specificationCasesTerm = search.getWorkingTerm().sub(1);
      Term excDefinition = search.getExceptionDefinition();
      Term normalExcDefinition;
      Term exceptionalExcDefinition;
      if (excDefinition.op() == Junctor.NOT) {
         exceptionalExcDefinition = excDefinition;
         normalExcDefinition = search.getExceptionEquality();
      }
      else {
         normalExcDefinition = excDefinition;
         exceptionalExcDefinition = services.getTermBuilder().not(excDefinition);
      }
      collectSpecifcationCasesPreconditions(normalExcDefinition, exceptionalExcDefinition, specificationCasesTerm, normalConditions, exceptinalConditions);
   }

   /**
    * Collects recursively the preconditions of specification cases.
    * @param normalExcDefinition The normal exception equality.
    * @param exceptionalExcDefinition The exceptional equality.
    * @param term The current {@link Term}.
    * @param normalConditions The {@link List} with the normal case conditions to fill.
    * @param exceptinalConditions The {@link List} with the exceptional case conditions to fill.
    * @throws ProofInputException Occurred Exception.
    */
   private static void collectSpecifcationCasesPreconditions(Term normalExcDefinition, 
                                                             Term exceptionalExcDefinition, 
                                                             Term term,
                                                             List<Term> normalConditions,
                                                             List<Term> exceptinalConditions) throws ProofInputException {
      if (term.op() == Junctor.AND) {
         Term lastChild = term.sub(term.arity() - 1);
         if (lastChild.equals(normalExcDefinition) || lastChild.equals(exceptionalExcDefinition)) {
            // Nothing to do, condition is just true
         }
         else {
            Term firstChild = term.sub(0);
            if (firstChild.equals(normalExcDefinition) || firstChild.equals(exceptionalExcDefinition)) {
               // Nothing to do, condition is just true
            }
            else {
               for (int i = 0; i < term.arity(); i++) {
                  collectSpecifcationCasesPreconditions(normalExcDefinition, exceptionalExcDefinition, term.sub(i), normalConditions, exceptinalConditions);
               }
            }
         }
      }
      else if (term.op() == Junctor.IMP) {
         Term leftTerm = term.sub(0);
         if (leftTerm.equals(normalExcDefinition) || leftTerm.equals(exceptionalExcDefinition)) {
            // Nothing to do, condition is just true
         }
         else {
            Term rightTerm = term.sub(1);
            // Check if condition is used for normal and exceptional case
            if (rightTerm.op() == Junctor.AND &&
                rightTerm.sub(0).op() == Junctor.IMP &&
                rightTerm.sub(0).sub(0).equals(normalExcDefinition) &&
                rightTerm.sub(1).op() == Junctor.IMP &&
                rightTerm.sub(1).sub(0).equals(exceptionalExcDefinition)) {
               normalConditions.add(leftTerm);
               exceptinalConditions.add(leftTerm);
            }
            else {
               Term excCondition = rightTerm;
               // Check if right child is exception definition
               if (excCondition.op() == Junctor.AND) {
                  excCondition = excCondition.sub(excCondition.arity() - 1);
               }
               if (excCondition.equals(normalExcDefinition)) {
                  normalConditions.add(leftTerm);
               }
               else if (excCondition.equals(exceptionalExcDefinition)) {
                  exceptinalConditions.add(leftTerm);
               }
               else {
                  // Check if left child is exception definition
                  if (rightTerm.op() == Junctor.AND) {
                     excCondition = rightTerm.sub(0);
                     if (excCondition.equals(normalExcDefinition)) {
                        normalConditions.add(leftTerm);
                     }
                     else if (excCondition.equals(exceptionalExcDefinition)) {
                        exceptinalConditions.add(leftTerm);
                     }
                     else {
                        throw new ProofInputException("Exeptional condition expected, implementation of UseOperationContractRule might has changed!"); 
                     }
                  }
                  else {
                     throw new ProofInputException("Exeptional condition expected, implementation of UseOperationContractRule might has changed!"); 
                  }
               }
            }
         }
      }
   }

   /**
    * Searches the used exception variable in the post or exceptional post branch of an applied {@link ContractRuleApp} on the parent of the given {@link Node}. 
    * @param node The {@link Node} which is the post or exceptional post branch of an applied {@link ContractRuleApp}.
    * @param services The {@link Services} to use.
    * @return The result.
    * @throws ProofInputException Occurred exception if something is not as expected.
    */
   public static ContractPostOrExcPostExceptionVariableResult searchContractPostOrExcPostExceptionVariable(Node node, Services services) throws ProofInputException {
      Semisequent antecedent = node.sequent().antecedent();
      SequentFormula sf = antecedent.get(antecedent.size() - 1);
      Term workingTerm = sf.formula();
      Pair<ImmutableList<Term>,Term> updatesAndTerm = TermBuilder.goBelowUpdates2(workingTerm);
      workingTerm = updatesAndTerm.second;
      if (workingTerm.op() != Junctor.AND) {
         throw new ProofInputException("And operation expected, implementation of UseOperationContractRule might has changed!"); 
      }
      workingTerm = workingTerm.sub(1); // First part is heap equality, use second part which is the combination of all normal and exceptional preconditon postcondition implications
      workingTerm = TermBuilder.goBelowUpdates(workingTerm);
      // Find Term exc_n = null which is added (maybe negated) to all exceptional preconditions
      Term exceptionDefinition = searchExceptionDefinition(workingTerm, services);
      if (exceptionDefinition == null) {
         throw new ProofInputException("Exception definition not found, implementation of UseOperationContractRule might has changed!"); 
      }
      // Make sure that exception equality was found
      Term exceptionEquality = exceptionDefinition.op() == Junctor.NOT ?
                               exceptionDefinition.sub(0) :
                               exceptionDefinition;
      return new ContractPostOrExcPostExceptionVariableResult(workingTerm, updatesAndTerm, exceptionDefinition, exceptionEquality);
   }
   
   /**
    * Searches the exception definition.
    * @param term The {@link Term} to start search in.
    * @param services the {@link Services} to use.
    * @return The found exception definition or {@code null} if not available.
    */
   private static Term searchExceptionDefinition(Term term, Services services) {
      if (term.op() == Equality.EQUALS && 
          term.sub(0).op() instanceof LocationVariable && 
          term.sub(0).toString().startsWith("exc_") &&
          isNullSort(term.sub(1).sort(), services) &&
          services.getJavaInfo().isSubtype(services.getJavaInfo().getKeYJavaType(term.sub(0).sort()), services.getJavaInfo().getKeYJavaType("java.lang.Throwable"))) {
         return term;
      }
      else {
         Term result = null;
         int i = term.arity() - 1;
         while (result == null && i >= 0) {
            result = searchExceptionDefinition(term.sub(i), services);
            i--;
         }
         return result;
      }
   }
   
   /**
    * The result of {@link SymbolicExecutionUtil#searchContractPostOrExcPostExceptionVariable(Node, Services)}.
    * @author Martin Hentschel
    */
   public static class ContractPostOrExcPostExceptionVariableResult {
      /**
       * The working {@link Term}.
       */
      private Term workingTerm;
      
      /**
       * The updates.
       */
      private Pair<ImmutableList<Term>,Term> updatesAndTerm;
      
      /**
       * The exception definition.
       */
      private Term exceptionDefinition;
      
      /**
       * The equality which contains the equality.
       */
      private Term exceptionEquality;
      
      /**
       * Constructor.
       * @param workingTerm The working {@link Term}.
       * @param updatesAndTerm The updates.
       * @param exceptionDefinition The exception definition.
       * @param exceptionEquality The equality which contains the equality.
       */
      public ContractPostOrExcPostExceptionVariableResult(Term workingTerm, 
                                                          Pair<ImmutableList<Term>, Term> updatesAndTerm, 
                                                          Term exceptionDefinition,
                                                          Term exceptionEquality) {
         this.workingTerm = workingTerm;
         this.updatesAndTerm = updatesAndTerm;
         this.exceptionDefinition = exceptionDefinition;
         this.exceptionEquality = exceptionEquality;
      }
      
      /**
       * Returns the working {@link Term}.
       * @return The working {@link Term}.
       */
      public Term getWorkingTerm() {
         return workingTerm;
      }

      /**
       * Returns the updates.
       * @return The updates.
       */
      public Pair<ImmutableList<Term>, Term> getUpdatesAndTerm() {
         return updatesAndTerm;
      }
      
      /**
       * Returns the exception definition.
       * @return The exception definition.
       */
      public Term getExceptionDefinition() {
         return exceptionDefinition;
      }
      
      /**
       * Returns the equality which contains the equality.
       * @return The equality which contains the equality.
       */
      public Term getExceptionEquality() {
         return exceptionEquality;
      }
   }
   
   /**
    * <p>
    * Computes the branch condition of the given {@link Node} which was constructed by a {@link LoopInvariantBuiltInRuleApp}.
    * </p>
    * <p>
    * The branch conditions are:
    * <ul>
    *    <li>Preserves Branch: Invariant + LoopCondition</li>
    *    <li>Use Branch: Invariant + !LoopCondition</li>
    * </ul>
    * </p>
    * @param parent The parent {@link Node} of the given one.
    * @param node The {@link Node} to compute its branch condition.
    * @param simplify {@code true} simplify condition in a side proof, {@code false} do not simplify condition.
    * @param improveReadability {@code true} improve readability, {@code false} do not improve readability.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   private static Term computeLoopInvariantBuiltInRuleAppBranchCondition(Node parent,
                                                                         Node node,
                                                                         boolean simplify,
                                                                         boolean improveReadability) throws ProofInputException {
      // Make sure that a computation is possible
      if (!(parent.getAppliedRuleApp() instanceof LoopInvariantBuiltInRuleApp)) {
         throw new ProofInputException("Only LoopInvariantBuiltInRuleApp is allowed in branch computation but rule \"" + parent.getAppliedRuleApp() + "\" was found.");
      }
      // Make sure that branch is supported
      int childIndex = CollectionUtil.indexOf(parent.childrenIterator(), node);
      if (childIndex == 1 || childIndex == 2) { // Body Preserves Invariant or Use Case
         LoopInvariantBuiltInRuleApp app = (LoopInvariantBuiltInRuleApp)parent.getAppliedRuleApp();
         // Compute invariant (last antecedent formula of the use branch)
         Services services = parent.proof().getServices();
         Node useNode = parent.child(2);
         Semisequent antecedent = useNode.sequent().antecedent();
         Term invTerm = antecedent.get(antecedent.size() - 1).formula();
         // Extract loop condition from child
         Term loopConditionModalityTerm = posInOccurrenceInOtherNode(parent, app.posInOccurrence(), node);
         Pair<ImmutableList<Term>,Term> pair = TermBuilder.goBelowUpdates2(loopConditionModalityTerm);
         loopConditionModalityTerm = pair.second;
         if (childIndex == 1) { // Body Preserves Invariant
            if (loopConditionModalityTerm.op() != Junctor.IMP) {
               throw new ProofInputException("Implementation of WhileInvariantRule has changed."); 
            }
            loopConditionModalityTerm = loopConditionModalityTerm.sub(0);
         }
         else { // Use Case
            if (loopConditionModalityTerm.op() != Modality.BOX) {
               throw new ProofInputException("Implementation of WhileInvariantRule has changed."); 
            }
            Term sub = loopConditionModalityTerm.sub(0);
            if (sub.op() != Junctor.IMP) {
               throw new ProofInputException("Implementation of WhileInvariantRule has changed."); 
            }
            loopConditionModalityTerm = services.getTermBuilder().box(loopConditionModalityTerm.javaBlock(), sub.sub(0));
         }
         if (loopConditionModalityTerm.op() != Modality.BOX ||
             loopConditionModalityTerm.sub(0).op() != Equality.EQUALS ||
             !(loopConditionModalityTerm.sub(0).sub(0).op() instanceof LocationVariable) ||
             loopConditionModalityTerm.sub(0).sub(1).op() != (childIndex == 1 ? services.getTermBuilder().TRUE().op() : services.getTermBuilder().FALSE().op())) {
            throw new ProofInputException("Implementation of WhileInvariantRule has changed."); 
         }
         // Create formula which contains the value interested in.
         invTerm = TermBuilder.goBelowUpdates(invTerm);
         Term loopCondAndInv = services.getTermBuilder().and(loopConditionModalityTerm.sub(0), invTerm);
         Term newTerm = loopCondAndInv;
         Term modalityTerm = childIndex == 1 ?
                             services.getTermBuilder().box(loopConditionModalityTerm.javaBlock(), newTerm) :
                             services.getTermBuilder().dia(loopConditionModalityTerm.javaBlock(), newTerm);
         Term condition;
         if (simplify) {
            final ProofEnvironment sideProofEnv = SymbolicExecutionSideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(parent.proof(), true); // New OneStepSimplifier is required because it has an internal state and the default instance can't be used parallel.
            Sequent newSequent = createSequentToProveWithNewSuccedent(parent, (Term)null, modalityTerm, pair.first, true);
            condition = evaluateInSideProof(services, 
                                            parent.proof(), 
                                            sideProofEnv,
                                            newSequent, 
                                            RESULT_LABEL, 
                                            "Loop invariant branch condition computation on node " + parent.serialNr() + " for branch " + node.serialNr() + ".",
                                            StrategyProperties.SPLITTING_OFF);
         }
         else {
            condition = services.getTermBuilder().applySequential(pair.first, modalityTerm);
         }
         if (improveReadability) {
            condition = improveReadability(condition, services);
         }
         return condition;
      }
      else {
         throw new ProofInputException("Branch condition of initially valid check is not supported."); 
      }
   }

   /**
    * Returns the {@link Term} described by the given {@link PosInOccurrence} of the original {@link Node}
    * in the {@link Node} to apply on.
    * @param original The original {@link Node} on which the given {@link PosInOccurrence} works.
    * @param pio The given {@link PosInOccurrence}.
    * @param toApplyOn The new {@link Node} to apply the {@link PosInOccurrence} on.
    * @return The {@link Term} in the other {@link Node} described by the {@link PosInOccurrence} or {@code null} if not available.
    */
   public static Term posInOccurrenceInOtherNode(Node original, PosInOccurrence pio, Node toApplyOn) {
      if (original != null && toApplyOn != null) {
         return posInOccurrenceInOtherNode(original.sequent(), pio, toApplyOn.sequent());
      }
      else {
         return null;
      }
   }

   /**
    * Returns the {@link Term} described by the given {@link PosInOccurrence} of the original {@link Sequent}
    * in the {@link Sequent} to apply on.
    * @param original The original {@link Sequent} on which the given {@link PosInOccurrence} works.
    * @param pio The given {@link PosInOccurrence}.
    * @param toApplyOn The new {@link Sequent} to apply the {@link PosInOccurrence} on.
    * @return The {@link Term} in the other {@link Sequent} described by the {@link PosInOccurrence} or {@code null} if not available.
    */
   public static Term posInOccurrenceInOtherNode(Sequent original, PosInOccurrence pio,
                                                 Sequent toApplyOn) {
      if (original != null && pio != null && toApplyOn != null) {
         // Search index of formula in original sequent
         SequentFormula originalSF = pio.constrainedFormula();
         boolean antecendet = pio.isInAntec();
         int index;
         if (antecendet) {
            index = original.antecedent().indexOf(originalSF);
         }
         else {
            index = original.succedent().indexOf(originalSF);
         }
         if (index >= 0) {
            SequentFormula toApplyOnSF =
                    (antecendet ? toApplyOn.antecedent() : toApplyOn.succedent()).get(index);
            return toApplyOnSF.formula().subAt(pio.posInTerm());
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
    * Computes the branch condition of the given {@link Node} which was constructed by a {@link TacletApp}.
    * @param parent The parent {@link Node} of the given one.
    * @param node The {@link Node} to compute its branch condition.
    * @param simplify {@code true} simplify condition in a side proof, {@code false} do not simplify condition.
    * @param improveReadability {@code true} improve readability, {@code false} do not improve readability.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   private static Term computeTacletAppBranchCondition(Node parent,
                                                       Node node,
                                                       boolean simplify,
                                                       boolean improveReadability) throws ProofInputException {
      if (!(parent.getAppliedRuleApp() instanceof TacletApp)) {
         throw new ProofInputException("Only TacletApp is allowed in branch computation but rule \"" + parent.getAppliedRuleApp() + "\" was found.");
      }
      TacletApp app = (TacletApp)parent.getAppliedRuleApp();
      Services services = node.proof().getServices();
      // List new sequent formulas in the child node.
      ImmutableList<Term> newAntecedents = listNewSemisequentTerms(parent.sequent().antecedent(), node.sequent().antecedent());
      ImmutableList<Term> newSuccedents = listNewSemisequentTerms(parent.sequent().succedent(), node.sequent().succedent());
      // Find goal template which has created the represented proof node
      int childIndex = CollectionUtil.indexOf(parent.childrenIterator(), node);
      TacletGoalTemplate goalTemplate;
      if (app.taclet().goalTemplates().size() + 1 == parent.childrenCount()) {
         if (childIndex == 0) {
            goalTemplate = null;
         }
         else {
            goalTemplate = app.taclet().goalTemplates().take(app.taclet().goalTemplates().size() - childIndex).head();
         }
      }
      else {
         goalTemplate = app.taclet().goalTemplates().take(app.taclet().goalTemplates().size() - 1 - childIndex).head();
      }
      // Instantiate replace object if required
      if (goalTemplate != null) {
         if (goalTemplate.replaceWithExpressionAsObject() instanceof Sequent) {
            // Remove replace part of symbolic execution rules
            if (NodeInfo.isSymbolicExecution(app.taclet())) {
               Sequent sequent = (Sequent) goalTemplate.replaceWithExpressionAsObject();
               for (SequentFormula sf : sequent.antecedent()) {
                  Term replaceTerm = instantiateTerm(node, sf.formula(), app, services);
                  replaceTerm = services.getTermBuilder().applyUpdatePairsSequential(app.instantiations().getUpdateContext(), replaceTerm);
                  Term originalTerm = findReplacement(node.sequent().antecedent(), app.posInOccurrence(), replaceTerm);
                  assert originalTerm != null;
                  newAntecedents = newAntecedents.removeFirst(originalTerm);
               }
               for (SequentFormula sf : sequent.succedent()) {
                  Term replaceTerm = instantiateTerm(node, sf.formula(), app, services);
                  replaceTerm = services.getTermBuilder().applyUpdatePairsSequential(app.instantiations().getUpdateContext(), replaceTerm);
                  Term originalTerm = findReplacement(node.sequent().succedent(), app.posInOccurrence(), replaceTerm);
                  assert originalTerm != null;
                  newSuccedents = newSuccedents.removeFirst(originalTerm);
               }
            }
         }
         else if (goalTemplate.replaceWithExpressionAsObject() instanceof Term) {
            Term replaceTerm = (Term)goalTemplate.replaceWithExpressionAsObject();
            replaceTerm = instantiateTerm(node, replaceTerm, app, services);
            Term originalTerm = findReplacement(app.posInOccurrence().isInAntec() ? node.sequent().antecedent() : node.sequent().succedent(),
                                                app.posInOccurrence(),
                                                replaceTerm);
            assert originalTerm != null;
            if (app.posInOccurrence().isInAntec()) {
               newAntecedents = newAntecedents.removeFirst(originalTerm);
            }
            else {
               newSuccedents = newSuccedents.removeFirst(originalTerm);
            }
            if (!NodeInfo.isSymbolicExecution(app.taclet())) {
               // Make sure that an PosTacletApp was applied
               if (!(app instanceof PosTacletApp)) {
                  throw new ProofInputException("Only PosTacletApp are allowed with a replace term in branch computation but rule \"" + app + "\" was found.");
               }
               // Create new lists
               ImmutableList<Term> tempAntecedents = ImmutableSLList.nil();
               ImmutableList<Term> tempSuccedents = ImmutableSLList.nil();
               // Apply updates on antecedents and add result to new antecedents list
               for (Term a : newAntecedents) {
                  tempAntecedents = tempAntecedents.append(services.getTermBuilder().applyUpdatePairsSequential(app.instantiations().getUpdateContext(), a));
               }
               // Apply updates on succedents and add result to new succedents list
               for (Term suc : newSuccedents) {
                  tempSuccedents = tempSuccedents.append(services.getTermBuilder().applyUpdatePairsSequential(app.instantiations().getUpdateContext(), suc));
               }
               // Add additional equivalenz term to antecedent with the replace object which must be equal to the find term 
               replaceTerm = followPosInOccurrence(app.posInOccurrence(), originalTerm);
               replaceTerm = services.getTermBuilder().equals(replaceTerm, app.posInOccurrence().subTerm());
               replaceTerm = services.getTermBuilder().applyUpdatePairsSequential(app.instantiations().getUpdateContext(), replaceTerm);
               if (!tempAntecedents.contains(replaceTerm)) {
                  tempAntecedents = tempAntecedents.append(replaceTerm);
               }
               // Replace old with new lists
               newAntecedents = tempAntecedents;
               newSuccedents = tempSuccedents;
            }      
         }
         else if (goalTemplate.replaceWithExpressionAsObject() != null) {
            throw new ProofInputException("Expected replacement as Sequent or Term during branch condition computation but is \"" + goalTemplate.replaceWithExpressionAsObject() + "\".");
         }
      }
      // Compute branch condition
      Term newLeft = services.getTermBuilder().and(newAntecedents);
      Term newRight = services.getTermBuilder().or(newSuccedents);
      Term newLeftAndRight = services.getTermBuilder().and(newLeft, services.getTermBuilder().not(newRight));
      // Simplify condition if required
      Term condition;
      if (simplify) {
         // Create formula which contains the value interested in.
         final ProofEnvironment sideProofEnv = SymbolicExecutionSideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(parent.proof(), true); // New OneStepSimplifier is required because it has an internal state and the default instance can't be used parallel.
         Sequent newSequent = createSequentToProveWithNewSuccedent(parent, null, (Term)null, newLeftAndRight, true);
         condition = evaluateInSideProof(services, 
                                         parent.proof(), 
                                         sideProofEnv,
                                         newSequent, 
                                         RESULT_LABEL, 
                                         "Taclet branch condition computation on node " + parent.serialNr() + " for branch " + node.serialNr() + ".",
                                         StrategyProperties.SPLITTING_OFF);
      }
      else {
         condition = newLeftAndRight;
      }
      if (improveReadability) {
         condition = improveReadability(condition, services);
      }
      return condition;
   }

   /**
    * Lists the {@link Term}s of all new {@link SequentFormula} in the child {@link Semisequent}.
    * @param parent The parent {@link Semisequent}.
    * @param child The child {@link Semisequent}.
    * @return An {@link ImmutableList} with all new {@link Term}s.
    */
   private static ImmutableList<Term> listNewSemisequentTerms(Semisequent parent, 
                                                              Semisequent child) {
      Set<SequentFormula> parentSFs = new HashSet<SequentFormula>();
      for (SequentFormula sf : parent) {
         parentSFs.add(sf);
      }
      ImmutableList<Term> result = ImmutableSLList.nil();
      for (SequentFormula sf : child) {
         if (!parentSFs.contains(sf)) {
            result = result.append(sf.formula());
         }
      }
      return result;
   }
   
   /**
    * Searches the by {@link Rule} application instantiated replace {@link Term}
    * which is equal modulo labels to the given replace {@link Term}.
    * @param terms The available candidates created by {@link Rule} application.
    * @param posInOccurrence The {@link PosInOccurrence} on which the rule was applied.
    * @param replaceTerm The {@link Term} to find.
    * @return The found {@link Term} or {@code null} if not available.
    */
   private static Term findReplacement(Semisequent semisequent, 
                                       final PosInOccurrence posInOccurrence, 
                                       final Term replaceTerm) {
      SequentFormula sf = CollectionUtil.search(semisequent, new IFilter<SequentFormula>() {
         @Override
         public boolean select(SequentFormula element) {
            return checkReplaceTerm(element.formula(), posInOccurrence, replaceTerm);
         }
      });
      return sf != null ? sf.formula() : null;
   }

   /**
    * Checks if the given replace {@link Term} is equal module labels to the {@link Term} to check.
    * @param toCheck The {@link Term} to check.
    * @param posInOccurrence The {@link PosInOccurrence} of the {@link Rule} application.
    * @param replaceTerm The {@link Term} to compare with.
    * @return {@code true} equal modulo labels, {@code false} not equal at all.
    */
   private static boolean checkReplaceTerm(Term toCheck, PosInOccurrence posInOccurrence, Term replaceTerm) {
      Term termAtPio = followPosInOccurrence(posInOccurrence, toCheck);
      if (termAtPio != null) {
         return termAtPio.equalsModRenaming(replaceTerm);
      }
      else {
         return false;
      }
   }
   
   /**
    * Returns the sub {@link Term} at the given {@link PosInOccurrence} 
    * but on the given {@link Term} instead of the one contained in the {@link PosInOccurrence}.
    * @param posInOccurrence The {@link PosInOccurrence} which defines the sub term position.
    * @param term The {@link Term} to work with.
    * @return The found sub {@link Term} or {@code null} if the {@link PosInOccurrence} is not compatible.
    */
   public static Term followPosInOccurrence(PosInOccurrence posInOccurrence, Term term) {
      boolean matches = true;
      IntIterator iter = posInOccurrence.posInTerm().iterator();
      while (matches && iter.hasNext()) {
         int index = iter.next();
         if (index < term.arity()) {
            term = term.sub(index);
         }
         else {
            matches = false;
         }
      }
      return matches ? term : null;
   }

   /**
    * Instantiates the given {@link Term} of the applied {@link TacletApp}.
    * @param node The current {@link Node}.
    * @param term The {@link Term} to instantiate.
    * @param tacletApp The {@link TacletApp} to consider.
    * @param services The {@link Services} to use.
    * @return The instantiated {@link Term} or {@code null} if no {@link Term} was given.
    */
   public static Term instantiateTerm(Node node,
                                      Term term, 
                                      TacletApp tacletApp, 
                                      Services services) {
      if (term != null) {
         SyntacticalReplaceVisitor visitor = new SyntacticalReplaceVisitor(new TermLabelState(), null, tacletApp.posInOccurrence(), tacletApp.instantiations(), null, tacletApp.taclet(), services);
         term.execPostOrder(visitor);
         return visitor.getTerm();
      }
      else {
         return null;
      }
   }

   /**
    * Starts the side proof and evaluates the {@link Sequent} to prove into a single {@link Term}.
    * @param services The {@link Services} to use.
    * @param proof The {@link Proof} from on which the side proof si performed.
    * @param sequentToProve The {@link Sequent} to prove in a side proof.
    * @param label The {@link TermLabel} which is used to compute the result.
    * @param description The side proof description.
    * @param splittingOption The splitting options to use.
    * @return The result {@link Term}.
    * @throws ProofInputException Occurred Exception.
    */
   private static Term evaluateInSideProof(Services services, 
                                           Proof proof, 
                                           ProofEnvironment sideProofEnvironment,
                                           Sequent sequentToProve, 
                                           TermLabel label, 
                                           String description, 
                                           String splittingOption) throws ProofInputException {
      List<Pair<Term, Node>> resultValuesAndConditions = SymbolicExecutionSideProofUtil.computeResults(services, 
                                                                                      proof, 
                                                                                      sideProofEnvironment,
                                                                                      sequentToProve, 
                                                                                      label, 
                                                                                      description, 
                                                                                      StrategyProperties.METHOD_NONE, // Stop at methods to avoid endless executions and scenarios in which a precondition or null pointer check can't be shown
                                                                                      StrategyProperties.LOOP_NONE, // Stop at loops to avoid endless executions and scenarios in which the invariant can't be shown to be initially valid or preserved.
                                                                                      StrategyProperties.QUERY_OFF, // Stop at queries to to avoid endless executions and scenarios in which a precondition or null pointer check can't be shown
                                                                                      splittingOption, 
                                                                                      false);
      ImmutableList<Term> goalCondtions = ImmutableSLList.<Term>nil();
      for (Pair<Term, Node> pair : resultValuesAndConditions) {
         Term goalCondition = pair.first;
         goalCondition = SymbolicExecutionUtil.replaceSkolemConstants(pair.second.sequent(), goalCondition, services);
         goalCondition = removeLabelRecursive(services.getTermFactory(), goalCondition, label);
         goalCondtions = goalCondtions.append(goalCondition);
      }
      return services.getTermBuilder().and(goalCondtions);
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
      HashMap<String, String> clone = new LinkedHashMap<String, String>();
      clone.putAll(settings);
      clone.put(key, value);
      ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().setDefaultChoices(clone);
   }

   /**
    * Checks if the given {@link Term} is null in the {@link Sequent} of the given {@link Node}. 
    * @param node The {@link Node} which provides the original {@link Sequent}
    * @param additionalAntecedent An additional antecedent.
    * @param newSuccedent The {@link Term} to check.
    * @return {@code true} {@link Term} was evaluated to null, {@code false} {@link Term} was not evaluated to null.
    * @throws ProofInputException Occurred Exception
    */
   public static boolean isNull(Node node, 
                                Term additionalAntecedent, 
                                Term newSuccedent) throws ProofInputException {
      return checkNull(node, additionalAntecedent, newSuccedent, true);
   }

   /**
    * Checks if the given {@link Term} is not null in the {@link Sequent} of the given {@link Node}. 
    * @param node The {@link Node} which provides the original {@link Sequent}
    * @param additionalAntecedent An additional antecedent.
    * @param newSuccedent The {@link Term} to check.
    * @return {@code true} {@link Term} was evaluated to not null, {@code false} {@link Term} was not evaluated to not null.
    * @throws ProofInputException Occurred Exception
    */
   public static boolean isNotNull(Node node, 
                                   Term additionalAntecedent, 
                                   Term newSuccedent) throws ProofInputException {
      return checkNull(node, additionalAntecedent, newSuccedent, false);
   }
   
   /**
    * Checks if the given {@link Term} is null or not in the {@link Sequent} of the given {@link Node}.
    * @param node The {@link Node} which provides the original {@link Sequent}
    * @param additionalAntecedent An additional antecedent.
    * @param newSuccedent The {@link Term} to check.
    * @param nullExpected {@code true} expect that {@link Term} is null, {@code false} expect that term is not null.
    * @return {@code true} term is null value matches the expected nullExpected value, {@code false} otherwise.
    * @throws ProofInputException Occurred Exception
    */
   private static boolean checkNull(Node node, 
                                    Term additionalAntecedent, 
                                    Term newSuccedent,
                                    boolean nullExpected) throws ProofInputException {
      // Make sure that correct parameters are given
      assert node != null;
      assert newSuccedent != null;
      // Create Sequent to prove
      final ProofEnvironment sideProofEnv = SymbolicExecutionSideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(node.proof(), true); // New OneStepSimplifier is required because it has an internal state and the default instance can't be used parallel.
      final TermBuilder tb = sideProofEnv.getServicesForEnvironment().getTermBuilder();
      Term isNull = tb.equals(newSuccedent, tb.NULL());
      Term isNotNull = tb.not(isNull);
      Sequent sequentToProve = createSequentToProveWithNewSuccedent(node, additionalAntecedent, nullExpected ? isNull : isNotNull, false);
      // Execute proof in the current thread
      ApplyStrategyInfo info = SymbolicExecutionSideProofUtil.startSideProof(node.proof(), 
                                                            sideProofEnv,
                                                            sequentToProve, 
                                                            StrategyProperties.METHOD_CONTRACT,
                                                            StrategyProperties.LOOP_INVARIANT,
                                                            StrategyProperties.QUERY_ON,
                                                            StrategyProperties.SPLITTING_NORMAL);
      try {
         return !info.getProof().openEnabledGoals().isEmpty();
      }
      finally {
         SymbolicExecutionSideProofUtil.disposeOrStore("Null check on node " + node.serialNr() + ".", info);
      }
   }
   
   /**
    * Creates a new {@link Sequent} which is a modification from the {@link Sequent}
    * of the given {@link Node} which contains the same information but a different succedent.
    * @param node The {@link Node} which provides the original {@link Sequent}.
    * @param newSuccedent The new succedent.
    * @return The created {@link Sequent}.
    */
   public static Sequent createSequentToProveWithNewSuccedent(Node node,
                                                              PosInOccurrence pio,
                                                              Term newSuccedent) {
      return createSequentToProveWithNewSuccedent(node, pio, null, newSuccedent, false);
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
                                                              Term newSuccedent,
                                                              boolean addResultLabel) {
      return createSequentToProveWithNewSuccedent(node, 
                                                  node.getAppliedRuleApp() != null ? node.getAppliedRuleApp().posInOccurrence() : null, 
                                                  additionalAntecedent, 
                                                  newSuccedent, 
                                                  addResultLabel);
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
                                                              PosInOccurrence pio,
                                                              Term additionalAntecedent,
                                                              Term newSuccedent,
                                                              boolean addResultLabel) {
      if (pio != null) {
         // Get the updates from the return node which includes the value interested in.
         ImmutableList<Term> originalUpdates;
         if (node.proof().root() == node) {
            originalUpdates = computeRootElementaryUpdates(node);
         }
         else {
            Term originalModifiedFormula = pio.constrainedFormula().formula();
            originalUpdates = TermBuilder.goBelowUpdates2(originalModifiedFormula).first;
         }
         // Create new sequent
         return createSequentToProveWithNewSuccedent(node, pio, additionalAntecedent, newSuccedent, originalUpdates, addResultLabel);
      }
      else {
         return createSequentToProveWithNewSuccedent(node, pio, additionalAntecedent, newSuccedent, null, addResultLabel);
      }
   }
   
   /**
    * Computes the initial {@link ElementaryUpdate}s on the given root {@link Node}.
    * @param root The root {@link Node} of the {@link Proof}.
    * @return The found initial {@link ElementaryUpdate}s.
    */
   public static ImmutableList<Term> computeRootElementaryUpdates(Node root) {
      ImmutableList<Term> result = ImmutableSLList.nil();
      Sequent sequent = root.sequent();
      for (SequentFormula sf : sequent.succedent()) {
         Term term = sf.formula();
         if (Junctor.IMP.equals(term.op())) {
            result = result.prepend(collectElementaryUpdates(term.sub(1)));
         }
      }
      return result;
   }

   /**
    * Collects the {@link ElementaryUpdate}s in the given {@link Term}.
    * @param term The {@link Term} to collect its updates.
    * @return The found {@link ElementaryUpdate}s.
    */
   public static ImmutableList<Term> collectElementaryUpdates(Term term) {
      if (term.op() instanceof UpdateApplication) {
         Term updateTerm = UpdateApplication.getUpdate(term);
         return collectElementaryUpdates(updateTerm);
      }
      else if (term.op() == UpdateJunctor.PARALLEL_UPDATE) {
         ImmutableList<Term> result = ImmutableSLList.nil();
         for (int i = 0; i < term.arity(); i++) {
            result = result.prepend(collectElementaryUpdates(term.sub(i)));
         }
         return result;
      }
      else if (term.op() instanceof ElementaryUpdate) {
         return ImmutableSLList.<Term>nil().prepend(term);
      }
      else {
         return ImmutableSLList.<Term>nil();
      }
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
                                                              ImmutableList<Term> updates,
                                                              boolean addResultLabel) {
      return createSequentToProveWithNewSuccedent(node, node.getAppliedRuleApp().posInOccurrence(), additionalAntecedent, newSuccedent, updates, addResultLabel);
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
                                                              PosInOccurrence pio,
                                                              Term additionalAntecedent,
                                                              Term newSuccedent,
                                                              ImmutableList<Term> updates,
                                                              boolean addResultLabel) {
      final TermBuilder tb = node.proof().getServices().getTermBuilder();
      // Combine method frame, formula with value predicate and the updates which provides the values
      Term newSuccedentToProve;
      if (updates != null) {
         if (newSuccedent != null) {
            newSuccedentToProve = tb.applySequential(updates, newSuccedent);
         }
         else {
            newSuccedentToProve = newSuccedent;
         }
      }
      else {
         newSuccedentToProve = newSuccedent;
      }
      // Create new sequent with the original antecedent and the formulas in the succedent which were not modified by the applied rule
      Sequent originalSequentWithoutMethodFrame = SymbolicExecutionSideProofUtil.computeGeneralSequentToProve(node.sequent(), pio != null ? pio.constrainedFormula() : null);
      Set<Term> skolemTerms = newSuccedentToProve != null ? 
                              collectSkolemConstants(originalSequentWithoutMethodFrame, newSuccedentToProve) :
                              collectSkolemConstants(originalSequentWithoutMethodFrame, tb.parallel(updates));
      originalSequentWithoutMethodFrame = removeAllUnusedSkolemEqualities(originalSequentWithoutMethodFrame, skolemTerms);
      if (addResultLabel) {
         TermFactory factory = node.proof().getServices().getTermFactory();
         Set<Term> skolemInNewTerm = collectSkolemConstantsNonRecursive(newSuccedentToProve);
         originalSequentWithoutMethodFrame = labelSkolemConstants(originalSequentWithoutMethodFrame, skolemInNewTerm, factory);
         newSuccedentToProve = addLabelRecursiveToNonSkolem(factory, newSuccedentToProve, RESULT_LABEL);
      }
      Sequent sequentToProve = newSuccedentToProve != null ?
                               originalSequentWithoutMethodFrame.addFormula(new SequentFormula(newSuccedentToProve), false, true).sequent() :
                               originalSequentWithoutMethodFrame;
      if (additionalAntecedent != null) {
         sequentToProve = sequentToProve.addFormula(new SequentFormula(additionalAntecedent), true, false).sequent();
      }
      return sequentToProve;
   }

   /**
    * Labels all specified skolem equalities with the {@link ParameterlessTermLabel#RESULT_LABEL}.
    * @param sequent The {@link Sequent} to modify.
    * @param constantsToLabel The skolem constants to label.
    * @param factory The {@link TermFactory} to use.
    * @return The modified {@link Sequent}.
    */
   protected static Sequent labelSkolemConstants(Sequent sequent, 
                                                 Set<Term> constantsToLabel, 
                                                 TermFactory factory) {
      for (SequentFormula sf : sequent.antecedent()) {
         int skolemEquality = checkSkolemEquality(sf);
         if (skolemEquality == -1) {
            Term equality = sf.formula();
            if (constantsToLabel.contains(equality.sub(0))) {
               Term definition = addLabelRecursiveToNonSkolem(factory, equality.sub(1), RESULT_LABEL);
               Term skolem = addLabelRecursiveToNonSkolem(factory, equality.sub(0), RESULT_LABEL);
               List<Term> newSubs = new LinkedList<Term>();
               newSubs.add(definition);
               newSubs.add(skolem);
               Term newEquality = factory.createTerm(equality.op(), new ImmutableArray<Term>(newSubs), equality.boundVars(), equality.javaBlock(), equality.getLabels());
               sequent = sequent.changeFormula(new SequentFormula(newEquality), new PosInOccurrence(sf, PosInTerm.getTopLevel(), true)).sequent();
            }
         }
         else if (skolemEquality == 1) {
            Term equality = sf.formula();
            if (constantsToLabel.contains(equality.sub(1))) {
               Term definition = addLabelRecursiveToNonSkolem(factory, equality.sub(0), RESULT_LABEL);
               Term skolem = addLabelRecursiveToNonSkolem(factory, equality.sub(1), RESULT_LABEL);
               List<Term> newSubs = new LinkedList<Term>();
               newSubs.add(definition);
               newSubs.add(skolem);
               Term newEquality = factory.createTerm(equality.op(), new ImmutableArray<Term>(newSubs), equality.boundVars(), equality.javaBlock(), equality.getLabels());
               sequent = sequent.changeFormula(new SequentFormula(newEquality), new PosInOccurrence(sf, PosInTerm.getTopLevel(), true)).sequent();
            }
         }
      }
      return sequent;
   }

   /**
    * Adds the given {@link TermLabel} to the given {@link Term} and to all of its children.
    * @param tf The {@link TermFactory} to use.
    * @param term The {@link Term} to add label to.
    * @param label The {@link TermLabel} to add.
    * @return A new {@link Term} with the given {@link TermLabel}.
    */
   private static Term addLabelRecursiveToNonSkolem(TermFactory tf, Term term, TermLabel label) {
      List<Term> newSubs = new LinkedList<Term>();
      for (Term oldSub : term.subs()) {
         newSubs.add(addLabelRecursiveToNonSkolem(tf, oldSub, label));
      }
      if (checkSkolemEquality(term) != 0 || isSkolemConstant(term)) {
         // Do not label skolem equality and skolem terms
         return tf.createTerm(term.op(), new ImmutableArray<Term>(newSubs), term.boundVars(), term.javaBlock(), term.getLabels());
      }
      else {
         /// Label term which is not a skolem equality and not a skolem term
         List<TermLabel> newLabels = new LinkedList<TermLabel>();
         for (TermLabel oldLabel : term.getLabels()) {
            newLabels.add(oldLabel);
         }
         newLabels.add(label);
         return tf.createTerm(term.op(), new ImmutableArray<Term>(newSubs), term.boundVars(), term.javaBlock(), new ImmutableArray<TermLabel>(newLabels));
      }
   }
   
   /**
    * Removes the given {@link TermLabel} from the given {@link Term} and from all of its children.
    * @param tf The {@link TermFactory} to use.
    * @param term The {@link Term} to remove label from.
    * @param label The {@link TermLabel} to remove.
    * @return A new {@link Term} without the given {@link TermLabel}.
    */
   public static Term removeLabelRecursive(TermFactory tf, Term term, TermLabel label) {
      // Update children
      List<Term> newSubs = new LinkedList<Term>();
      ImmutableArray<Term> oldSubs = term.subs();
      for (Term oldSub : oldSubs) {
         newSubs.add(removeLabelRecursive(tf, oldSub, label));
      }
      // Update label
      List<TermLabel> newLabels = new LinkedList<TermLabel>();
      ImmutableArray<TermLabel> oldLabels = term.getLabels();
      for (TermLabel oldLabel : oldLabels) {
         if (oldLabel != label) {
            newLabels.add(oldLabel);
         }
      }
      return tf.createTerm(term.op(), new ImmutableArray<Term>(newSubs), term.boundVars(), term.javaBlock(), new ImmutableArray<TermLabel>(newLabels));
   }

   /**
    * Collects all contained skolem {@link Term}s which fulfill
    * {@link #isSkolemConstant(Term)} as well as the skolem constants
    * used in the find once recursive.
    * @param sequent The {@link Sequent} which provides the skolem equalities.
    * @param term The {@link Term} to start collection in.
    * @return The found skolem {@link Term}s.
    */
   private static Set<Term> collectSkolemConstants(Sequent sequent, Term term) {
      if (term != null) {
         // Collect skolem constants in term
         Set<Term> result = collectSkolemConstantsNonRecursive(term);
         // Collect all skolem constants used in skolem constants
         List<Term> toCheck = new LinkedList<Term>(result);
         while (!toCheck.isEmpty()) {
            Term skolemConstant = toCheck.remove(0);
            List<Term> replacements = findSkolemReplacements(sequent, skolemConstant, null);
            for (Term replacement : replacements) {
               Set<Term> checkResult = collectSkolemConstantsNonRecursive(replacement);
               for (Term checkConstant : checkResult) {
                  if (result.add(checkConstant)) {
                     toCheck.add(checkConstant);
                  }
               }
            }
         }
         return result;
      }
      else {
         return new HashSet<Term>();
      }
   }

   /**
    * Collects all contained skolem {@link Term}s which fulfill
    * {@link #isSkolemConstant(Term)}.
    * @param term The {@link Term} to collect in.
    * @return The found skolem {@link Term}s.
    */
   private static Set<Term> collectSkolemConstantsNonRecursive(Term term) {
      final Set<Term> result = new HashSet<Term>();
      term.execPreOrder(new DefaultVisitor() {
         @Override
         public void visit(Term visited) {
            if (isSkolemConstant(visited)) {
               result.add(visited);
            }
         }
      });
      return result;
   }

   /**
    * Checks if the given {@link Term} is a skolem {@link Term} meaning
    * that it has the {@link SelectSkolemConstantTermLabel}.
    * @param term The {@link Term} to check.
    * @return {@code true} is skolem {@link Term}, {@code false} is not a skolem {@link Term}.
    */
   public static boolean isSkolemConstant(Term term) {
      return term.containsLabel(ParameterlessTermLabel.SELECT_SKOLEM_LABEL);
   }

   /**
    * Removes all {@link SequentFormula}s with a skolem equality from the given {@link Sequent}
    * if the skolem {@link Term} is not contained in the given {@link Collection}.
    * @param sequent The {@link Sequent} to modify.
    * @param skolemConstants The allowed skolem {@link Term}s.
    * @return The modified {@link Sequent} in which all not listed skolem {@link Term} equalites are removed.
    */
   private static Sequent removeAllUnusedSkolemEqualities(Sequent sequent,
                                                          Collection<Term> skolemConstants) {
      Sequent result = sequent;
      for (SequentFormula sf : sequent.antecedent()) {
         result = removeAllUnusedSkolemEqualities(result, sf, true, skolemConstants);
      }
      for (SequentFormula sf : sequent.succedent()) {
         result = removeAllUnusedSkolemEqualities(result, sf, false, skolemConstants);
      }
      return result;
   }

   /**
    * Helper method of {@link #removeAllUnusedSkolemEqualities(Sequent, Collection)}
    * which removes the given {@link SequentFormula} if required.
    * @param sequent The {@link Sequent} to modify.
    * @param sf The {@link SequentFormula} to remove if its skolem {@link Term} is not listed.
    * @param antecedent {@code true} antecedent, {@code false} succedent.
    * @param skolemConstants The allowed skolem {@link Term}s.
    * @return The modified {@link Sequent} in which the {@link SequentFormula} might be removed.
    */
   private static Sequent removeAllUnusedSkolemEqualities(Sequent sequent,
                                                          SequentFormula sf,
                                                          boolean antecedent,
                                                          Collection<Term> skolemConstants) {
      Term term = sf.formula();
      boolean remove = false;
      if (term.op() == Equality.EQUALS) {
         if (isSkolemConstant(term.sub(0))) {
            remove = !skolemConstants.contains(term.sub(0));
         }
         if (!remove && isSkolemConstant(term.sub(1))) {
            remove = !skolemConstants.contains(term.sub(1));
         }
      }
      if (remove) {
         return sequent.removeFormula(
                 new PosInOccurrence(sf, PosInTerm.getTopLevel(), antecedent)).sequent();
      }
      else {
         return sequent;
      }
   }

   /**
    * Checks if the given {@link SequentFormula} is a skolem equality.
    * @param sf The {@link SequentFormula} to check.
    * @return {@code -1} left side of skolem equality, {@code 0} no skolem equality, {@code 1} right side of skolem equality.
    */
   public static int checkSkolemEquality(SequentFormula sf) {
      return checkSkolemEquality(sf.formula());
   }

   /**
    * Checks if the given {@link Term} is a skolem equality.
    * @param sf The {@link Term} to check.
    * @return {@code -1} left side of skolem equality, {@code 0} no skolem equality, {@code 1} right side of skolem equality.
    */
   public static int checkSkolemEquality(Term term) {
      if (term.op() == Equality.EQUALS) {
         if (isSkolemConstant(term.sub(0))) {
            return -1;
         }
         if (isSkolemConstant(term.sub(1))) {
            return 1;
         }
      }
      return 0;
   }

   /**
    * Replaces all skolem constants in the given {@link Term}.
    * @param sequent The {@link Sequent} which provides the skolem equalities.
    * @param term The {@link Term} to replace its skolem constants.
    * @param services The {@link Services} to use.
    * @return The skolem constant free {@link Term}.
    */
   public static Term replaceSkolemConstants(Sequent sequent, Term term, Services services) {
      int skolemCheck = checkSkolemEquality(term);
      if (skolemCheck == -1) {
         TermBuilder tb = services.getTermBuilder();
         List<Term> replacements = findSkolemReplacements(sequent, term.sub(0), term);
         if (!replacements.isEmpty()) {
            Term other = term.sub(1);
            List<Term> newTerms = new LinkedList<Term>();
            for (Term replacement : replacements) {
               newTerms.add(tb.equals(replacement, other));
            }
            term = tb.and(newTerms);
            return replaceSkolemConstants(sequent, term, services);
         }
         else {
            return services.getTermBuilder().tt(); // If no other term is available the quality is jsut true.
         }
      }
      else if (skolemCheck == 1) {
         TermBuilder tb = services.getTermBuilder();
         List<Term> replacements = findSkolemReplacements(sequent, term.sub(1), term);
         if (!replacements.isEmpty()) {
            Term other = term.sub(0);
            List<Term> newTerms = new LinkedList<Term>();
            for (Term replacement : replacements) {
               newTerms.add(tb.equals(other, replacement));
            }
            term = tb.and(newTerms);
            return replaceSkolemConstants(sequent, term, services);
         }
         else {
            return services.getTermBuilder().tt(); // If no other term is available the quality is jsut true.
         }
      }
      else {
         if (isSkolemConstant(term)) {
            // Skolem term
            List<Term> replacements = findSkolemReplacements(sequent, term, null);
            return !replacements.isEmpty() ? 
                   replacements.get(0) : // Any of the replacements can be used, for simplicity use the first one. Alternatively may the one with the lowest depth or with least symbols might be used.
                   term;
         }
         else {
            // No skolem term
            List<Term> newChildren = new LinkedList<Term>();
            boolean changed = false;
            for (int i = 0; i < term.arity(); i++) {
               Term oldChild = term.sub(i);
               Term newChild = replaceSkolemConstants(sequent, oldChild, services);
               if (newChild != oldChild) {
                  changed = true;
               }
               newChildren.add(newChild);
            }
            if (changed) {
               if (term.op() == Junctor.NOT) {
                  // Create new NOT term using build in simplification of TermBuilder.
                  assert newChildren.size() == 1;
                  assert term.boundVars().isEmpty();
                  assert term.javaBlock() == JavaBlock.EMPTY_JAVABLOCK;
                  Term result = services.getTermBuilder().not(newChildren.get(0));
                  if (term.hasLabels()) {
                     result = services.getTermBuilder().label(result, term.getLabels());
                  }
                  return result;
               }
               else if (term.op() == Junctor.OR) {
                  // Create new OR term using build in simplification of TermBuilder.
                  assert term.boundVars().isEmpty();
                  assert term.javaBlock() == JavaBlock.EMPTY_JAVABLOCK;
                  Term result = services.getTermBuilder().or(newChildren);
                  if (term.hasLabels()) {
                     result = services.getTermBuilder().label(result, term.getLabels());
                  }
                  return result;
               }
               else if (term.op() == Junctor.AND) {
                  // Create new AND term using build in simplification of TermBuilder.
                  assert term.boundVars().isEmpty();
                  assert term.javaBlock() == JavaBlock.EMPTY_JAVABLOCK;
                  Term result = services.getTermBuilder().and(newChildren);
                  if (term.hasLabels()) {
                     result = services.getTermBuilder().label(result, term.getLabels());
                  }
                  return result;
               }
               else if (term.op() == Junctor.IMP) {
                  // Create new IMP term using build in simplification of TermBuilder.
                  assert newChildren.size() == 2;
                  assert term.boundVars().isEmpty();
                  assert term.javaBlock() == JavaBlock.EMPTY_JAVABLOCK;
                  return services.getTermBuilder().imp(newChildren.get(0), newChildren.get(1), term.getLabels());
               }
               else {
                  // Create new term in general.
                  return services.getTermFactory().createTerm(term.op(),
                                                              new ImmutableArray<Term>(newChildren),
                                                              term.boundVars(),
                                                              term.javaBlock(),
                                                              term.getLabels());
               }
            }
            else {
               return term;
            }
         }
      }
   }

   /**
    * Utility method of {@link #replaceSkolemConstants(Sequent, Term, Services)} to
    * find all equality parts of the given skolem constant.
    * @param sequent The {@link Sequent} which provides the skolem equalities.
    * @param skolemConstant The skolem constant to solve.
    * @param skolemEquality The optional skolem equality to ignore.
    * @return The equality parts of the given skolem equality.
    */
   private static List<Term> findSkolemReplacements(Sequent sequent, Term skolemConstant, Term skolemEquality) {
      List<Term> result = new LinkedList<Term>();
      for (SequentFormula sf : sequent) {
         Term term = sf.formula();
         if (term != skolemEquality) {
            int skolemCheck = checkSkolemEquality(term);
            if (skolemCheck == -1) {
               if (term.sub(0).equals(skolemConstant)) {
                  result.add(term.sub(1));
               }
            }
            else if (skolemCheck == 1) {
               if (term.sub(1).equals(skolemConstant)) {
                  result.add(term.sub(0));
               }
            }
         }
      }
      return result;
   }

   /**
    * Checks if the given {@link Sort} represents a {@code null} value in the given {@link Services}.
    * @param sort The {@link Sort} to check.
    * @param services The {@link Services} to use.
    * @return {@code true} is Null-Sort, {@code false} is something else.
    */
   public static boolean isNullSort(Sort sort, Services services) {
      return sort instanceof NullSort;
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
    * @param improveReadability {@code true} improve readability, {@code false} do not improve readability.
    * @return The computed path condition.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term computePathCondition(Node node,
                                           boolean improveReadability) throws ProofInputException {
      return computePathCondition(null, node, true, improveReadability);
   }

   /**
    * Computes the path condition between the given {@link Node}s.
    * @param parentNode The {@link Node} to stop path condition computation at.
    * @param childNode The {@link Node} to compute its path condition back to the parent.
    * @param simplify {@code true} simplify each branch condition in a side proof, {@code false} do not simplify branch conditions.
    * @param improveReadability {@code true} improve readability, {@code false} do not improve readability.
    * @return The computed path condition.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term computePathCondition(Node parentNode,
                                           Node childNode,
                                           boolean simplify,
                                           boolean improveReadability) throws ProofInputException {
      if (childNode != null) {
         final Services services = childNode.proof().getServices();
         Term pathCondition = services.getTermBuilder().tt();
         while (childNode != null && childNode != parentNode) {
            Node parent = childNode.parent();
            if (parent != null && parent.childrenCount() >= 2) {
               Term branchCondition = computeBranchCondition(childNode, simplify, improveReadability);
               pathCondition = services.getTermBuilder().and(branchCondition, pathCondition);
            }
            childNode = parent;
         }
         if (services.getTermBuilder().ff().equals(pathCondition)) {
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
   public static IExecutionNode<?> getRoot(IExecutionNode<?> executionNode) {
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
      PosInOccurrence modalityTermPIO = SymbolicExecutionUtil.findModalityWithMinSymbolicExecutionLabelId(root.sequent());
      Term modalityTerm = modalityTermPIO != null ? modalityTermPIO.subTerm() : null;
      if (modalityTerm != null) {
         modalityTerm = TermBuilder.goBelowUpdates(modalityTerm);
         JavaProgramElement updateContent = modalityTerm.javaBlock().program();
         if (updateContent instanceof StatementBlock) { // try catch inclusive
            ImmutableArray<? extends Statement> updateContentBody =
                    ((StatementBlock)updateContent).getBody();
            Try tryStatement = null;
            Iterator<? extends Statement> iter = updateContentBody.iterator();
            while (tryStatement == null && iter.hasNext()) {
               Statement next = iter.next();
               if (next instanceof Try) {
                  tryStatement = (Try)next;
               }
            }
            if (tryStatement != null) {
               if (tryStatement.getBranchCount() == 1
                       && tryStatement.getBranchList().get(0) instanceof Catch) {
                  Catch catchStatement = (Catch)tryStatement.getBranchList().get(0);
                  if (catchStatement.getBody() instanceof StatementBlock) {
                     StatementBlock  catchBlock = (StatementBlock)catchStatement.getBody();
                     if (catchBlock.getBody().size() == 1
                             && catchBlock.getBody().get(0) instanceof Assignment) {
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
      throw new IllegalStateException("Can't extract exception variable from proof.");
   }

   /**
    * Configures the proof to use the given settings.
    * @param proof The {@link Proof} to configure.
    * @param useOperationContracts {@code true} use operation contracts, {@code false} expand methods.
    * @param useLoopInvariants {@code true} use loop invariants, {@code false} expand loops.
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param useLoopInvariants {@code true} immediately alias checks, {@code false} alias checks never.
    */
   public static void updateStrategySettings(Proof proof, 
                                             boolean useOperationContracts,
                                             boolean useLoopInvariants,
                                             boolean nonExecutionBranchHidingSideProofs,
                                             boolean aliasChecksImmediately) {
      if (proof != null && !proof.isDisposed()) {
         String methodTreatmentValue = useOperationContracts ? 
                                       StrategyProperties.METHOD_CONTRACT : 
                                       StrategyProperties.METHOD_EXPAND;
         String loopTreatmentValue = useLoopInvariants ? 
                                     StrategyProperties.LOOP_INVARIANT : 
                                     StrategyProperties.LOOP_EXPAND;
         String nonExecutionBranchHidingValue =
                 nonExecutionBranchHidingSideProofs ?
                         StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_SIDE_PROOF :
                             StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OFF;
         String aliasChecksValue = aliasChecksImmediately ? 
                                   StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_IMMEDIATELY : 
                                   StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_NEVER;
         StrategyProperties sp =
                 proof.getSettings().getStrategySettings().getActiveStrategyProperties();
         sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, methodTreatmentValue);
         sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, loopTreatmentValue);
         sp.setProperty(StrategyProperties.SYMBOLIC_EXECUTION_NON_EXECUTION_BRANCH_HIDING_OPTIONS_KEY,
                        nonExecutionBranchHidingValue);
         sp.setProperty(StrategyProperties.SYMBOLIC_EXECUTION_ALIAS_CHECK_OPTIONS_KEY,
                        aliasChecksValue);
         updateStrategySettings(proof, sp);
      }
   }

   /**
    * Configures the proof to use the given {@link StrategyProperties}.
    * @param proof The {@link Proof} to configure.
    * @param sb The {@link StrategyProperties} to set.
    */
   public static void updateStrategySettings(Proof proof, 
                                             StrategyProperties sp) {
      if (proof != null && !proof.isDisposed()) {
         assert sp != null;
         ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
         proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
      }
   }

   /**
    * Checks if the choice settings are initialized.
    * @return {@code true} settings are initialized, {@code false} settings are not initialized.
    */
   public static boolean isChoiceSettingInitialised() {
      return ProofSettings.isChoiceSettingInitialised();
   }

   /**
    * Checks if the given node should be represented as loop body termination.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param ruleApp The {@link RuleApp} may used or not used in the rule.
    * @return {@code true} represent node as loop body termination, {@code false} represent node as something else. 
    */
   public static boolean isLoopBodyTermination(final Node node, RuleApp ruleApp) {
      boolean result = false;
      if (ruleApp instanceof OneStepSimplifierRuleApp) {
         // Check applied rules in protocol
         OneStepSimplifierRuleApp simplifierApp = (OneStepSimplifierRuleApp)ruleApp;
         if (simplifierApp.getProtocol() != null) {
            RuleApp terminationApp =
                  CollectionUtil.search(simplifierApp.getProtocol(), new IFilter<RuleApp>() {
               @Override
               public boolean select(RuleApp element) {
                  return isLoopBodyTermination(node, element);
               }
            });
            result = terminationApp != null;
         }
      }
      else if (hasLoopBodyTerminationLabel(ruleApp)) {
         if ("impRight".equals(MiscTools.getRuleDisplayName(ruleApp))) {
            result = true; // Implication removed (not done if left part is false)
         }
         else {
            Term term = ruleApp.posInOccurrence().subTerm();
            if (term.op() == Junctor.IMP && term.sub(0).op() == Junctor.TRUE) {
               result = true; // Left part is true
            }
         }
      }
      return result;
   }
   
   /**
    * Checks if the given {@link Operator} is a heap.
    * @param op The {@link Operator} to check.
    * @param heapLDT The {@link HeapLDT} which provides the available heaps.
    * @return {@code true} {@link Operator} is heap, {@code false} {@link Operator} is something else.
    */
   public static boolean isHeap(Operator op, HeapLDT heapLDT) {
      if (op instanceof SortedOperator) {
         final Sort opSort = ((SortedOperator) op).sort();
         return CollectionUtil.search(heapLDT.getAllHeaps(), new IFilter<LocationVariable>() {
            @Override
            public boolean select(LocationVariable element) {
               return opSort == element.sort();
            }
         }) != null;
      }
      else {
         return false;
      }
   }
   
   /**
    * Returns the path to the source file defined by the given {@link PositionInfo}.
    * @param posInfo The {@link PositionInfo} to extract source file from.
    * @return The source file name or {@code null} if not available.
    */
   public static String getSourcePath(PositionInfo posInfo) {
      return MiscTools.getSourcePath(posInfo);
   }

   /**
    * Checks if the given {@link Term} is a select on a heap.
    * @param services The {@link Services} to use.
    * @param term The {@link Term} to check.
    * @return {@code true} is select, {@code false} is something else.
    */
   public static boolean isSelect(Services services, Term term) {
      if (!isNullSort(term.sort(), services)) {
         Function select = services.getTypeConverter().getHeapLDT().getSelect(term.sort(), services);
         return select == term.op();
      }
      else {
         return false;
      }
   }

   /**
    * Checks if the given {@link Operator} is a number.
    * @param op The {@link Operator} to check.
    * @return {@code true} is number, {@code false} is something else.
    */
   public static boolean isNumber(Operator op) {
      if (op instanceof Function) {
         String[] numbers = {"#", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "Z", "neglit"};
         Arrays.sort(numbers);
         int index = Arrays.binarySearch(numbers, op.name().toString());
         return index >= 0;
      }
      else {
         return false;
      }
   }

   /**
    * Checks if the given {@link Operator} is a boolean.
    * @param op The {@link Operator} to check.
    * @return {@code true} is boolean, {@code false} is something else.
    */
   public static boolean isBoolean(Services services, Operator op) {
      BooleanLDT booleanLDT = services.getTypeConverter().getBooleanLDT();
      return booleanLDT.getFalseConst() == op ||
             booleanLDT.getTrueConst() == op;
   }

   /**
    * Returns the default taclet options for symbolic execution.
    * @return The default taclet options for symbolic execution.
    */
   public static HashMap<String, String> getDefaultTacletOptions() {
      return MiscTools.getDefaultTacletOptions();
   }
   
   /**
    * <p>
    * Converts the given {@link Term} into a {@link String} respecting {@link #isUsePretty()}.
    * </p>
    * <p>
    * The functionality is similar to {@link ProofSaver#printTerm(Term, Services, boolean)} but allows to set custom settings.
    * </p>
    * @param term The {@link Term} to convert.
    * @param services The {@link Services} to use.
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @return The {@link String} representation of the given {@link Term}.
    */
   public static String formatTerm(Term term, 
                                   Services services, 
                                   boolean useUnicode,
                                   boolean usePrettyPrinting) {
      if ((useUnicode || usePrettyPrinting) && services != null) {
         StringBuffer result;
         NotationInfo ni = new NotationInfo();
         LogicPrinter logicPrinter = new LogicPrinter(new ProgramPrinter(null), ni, services, true);
         logicPrinter.getNotationInfo().refresh(services, usePrettyPrinting, useUnicode);
         try {
             logicPrinter.printTerm(term);
         } catch(IOException ioe) {
             System.err.println(ioe);
         }
         result = logicPrinter.result();
         if (result.charAt(result.length()-1) == '\n')
             result.deleteCharAt(result.length()-1);
         return result.toString();
      }
      else {
         return term != null ? term.toString() : null;
      }
   }
   
   /**
    * Checks if pretty printing is enabled or not.
    * @return {@code true} pretty printing is enabled, {@code false} pretty printing is disabled.
    */
   public static boolean isUsePrettyPrinting() {
      return ProofIndependentSettings.isUsePrettyPrinting();
   }

   /**
    * Defines if pretty printing is enabled or not.
    * @param usePrettyPrinting {@code true} pretty printing is enabled, {@code false} pretty printing is disabled.
    */
   public static void setUsePrettyPrinting(boolean usePrettyPrinting) {
      ProofIndependentSettings.setUsePrettyPrinting(usePrettyPrinting);
   }

   /**
    * Checks if the {@link Goal} has applicable rules.
    * @param goal The {@link Goal} to check.
    * @return {@code true} has applicable rules, {@code false} no rules are applicable.
    */
   public static boolean hasApplicableRules(Goal goal) {
      return Goal.hasApplicableRules(goal);
   }

   /**
    * Computes the call stack size and the second statement
    * similar to {@link NodeInfo#computeActiveStatement(SourceElement)}.
    * @param ruleApp The {@link RuleApp}.
    * @return The computed call stack size and the second statement if available.
    */
   public static Pair<Integer, SourceElement> computeSecondStatement(RuleApp ruleApp) {
      if (ruleApp != null) {
         // Find inner most block
         SourceElement firstStatement = NodeInfo.computeFirstStatement(ruleApp);
         Deque<StatementBlock> blocks = new LinkedList<StatementBlock>();
         int methodFrameCount = 0;
         if (firstStatement != null) {
            if (firstStatement instanceof StatementBlock) {
               blocks.addFirst((StatementBlock) firstStatement);
            }
            SourceElement lastStatement = null;
            while (firstStatement instanceof ProgramPrefix && 
                   lastStatement != firstStatement) {
               lastStatement = firstStatement;
               firstStatement = firstStatement.getFirstElementIncludingBlocks();
               if (lastStatement instanceof MethodFrame) {
                  blocks.clear(); // Only block of inner most method frames are of interest.
                  methodFrameCount++;
               }
               if (firstStatement instanceof StatementBlock) {
                  blocks.addFirst((StatementBlock) firstStatement);
               }
            }
         }
         // Compute second statement
         StatementBlock block = null;
         while (!blocks.isEmpty() && (block == null || block.getChildCount() < 2)) {
            block = blocks.removeFirst();
         }
         if (block != null && block.getChildCount() >= 2) {
            return new Pair<Integer, SourceElement>(methodFrameCount, block.getChildAt(1));
         }
         else {
            return new Pair<Integer, SourceElement>(methodFrameCount, null);
         }
      }
      else {
         return null;
      }
   }

   /**
    * Compares the given {@link SourceElement}s including their {@link PositionInfo}s.
    * @param first The first {@link SourceElement}.
    * @param second The second {@link SourceElement}.
    * @return {@code true} both are equal and at the same {@link PositionInfo}, {@code false} otherwise.
    */
   public static boolean equalsWithPosition(SourceElement first, SourceElement second) {
      if (first != null && second != null) {
         if (first instanceof While) {
            if (second instanceof While) {
               // Special treatment for while because its position info is lost during prove, but maintained in its guard.
               return first.equals(second) &&
                      equalsWithPosition(((While) first).getGuard(), ((While) second).getGuard());
            }
            else {
               return false;
            }
         }
         else {
            // Compare all source elements including ints position info
            return first.equals(second) &&
                   ObjectUtil.equals(first.getPositionInfo(), second.getPositionInfo());
         }
      }
      else {
         return first == null && second == null;
      }
   }

   /**
    * Checks if the given {@link ProgramElement} contains the given {@link SourceElement}.
    * @param toSearchIn The {@link ProgramElement} to search in.
    * @param toSearch The {@link SourceElement} to search.
    * @param services The {@link Services} to use.
    * @return {@code true} contained, {@code false} not contained.
    */
   public static boolean containsStatement(ProgramElement toSearchIn, SourceElement toSearch, Services services) {
      if (toSearchIn != null) {
         ContainsStatementVisitor visitor = new ContainsStatementVisitor(toSearchIn, toSearch, services);
         visitor.start();
         return visitor.isContained();
      }
      else {
         return false;
      }
   }
   
   /**
    * Utilits class used by {@link SymbolicExecutionUtil#containsStatement(MethodFrame, ProgramElement, Services)}.
    * @author Martin Hentschel
    */
   private static class ContainsStatementVisitor extends JavaASTVisitor {
      /**
       * The {@link ProgramElement} to search.
       */
      private final SourceElement toSearch;
      
      /**
       * The result.
       */
      private boolean contained = false;
      
      /**
       * Constructor.
       * @param root The {@link ProgramElement} to start search in.
       * @param toSearch The {@link SourceElement} to search.
       * @param services The {@link Services} to use.
       */
      public ContainsStatementVisitor(ProgramElement root, SourceElement toSearch, Services services) {
         super(root, services);
         this.toSearch = toSearch;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void doDefaultAction(SourceElement se) {
         if (equalsWithPosition(se, toSearch)) { // Comparison by == is not possible since loops are recreated
            contained = true;
         }
      }

      /**
       * Returns the result.
       * @return {@code true} contained, {@code false} not contained.
       */
      public boolean isContained() {
         return contained;
      }
   }
   
   /**
    * Creates recursive a term which can be used to determine the value
    * of {@link #getProgramVariable()}.
    * @param services The {@link Services} to use.
    * @return The created term.
    */
   public static Term createSelectTerm(IExecutionVariable variable) {
      final Services services = variable.getServices();
      if (SymbolicExecutionUtil.isStaticVariable(variable.getProgramVariable())) {
         // Static field access
         Function function = services.getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)variable.getProgramVariable(), services);
         return services.getTermBuilder().staticDot(variable.getProgramVariable().sort(), function);
      }
      else {
         if (variable.getParentValue() == null) {
            // Direct access to a variable, so return it as term
            return services.getTermBuilder().var((ProgramVariable)variable.getProgramVariable());
         }
         else {
            Term parentTerm = variable.getParentValue().getVariable().createSelectTerm();
            if (variable.getProgramVariable() != null) {
               if (services.getJavaInfo().getArrayLength() == variable.getProgramVariable()) {
                  // Special handling for length attribute of arrays
                  Function function = services.getTypeConverter().getHeapLDT().getLength();
                  return services.getTermBuilder().func(function, parentTerm);
               }
               else {
                  // Field access on the parent variable
                  Function function = services.getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)variable.getProgramVariable(), services);
                  return services.getTermBuilder().dot(variable.getProgramVariable().sort(), parentTerm, function);
               }
            }
            else {
               // Special handling for array indices.
               return services.getTermBuilder().dotArr(parentTerm, variable.getArrayIndex());
            }
         }
      }
   }
   
   /**
    * Creates the {@link NotationInfo} for the given {@link IExecutionElement}.
    * @param element The {@link IExecutionElement} to create its {@link NotationInfo}.
    * @return The created {@link NotationInfo}.
    */
   public static NotationInfo createNotationInfo(IExecutionElement element) {
      Proof proof = element != null ? element.getProof() : null;
      return createNotationInfo(proof);
   }

   /**
    * Creates the {@link NotationInfo} for the given {@link Node}.
    * @param node The {@link Node} to create its {@link NotationInfo}.
    * @return The created {@link NotationInfo}.
    */
   public static NotationInfo createNotationInfo(Node node) {
      Proof proof = node != null ? node.proof() : null;
      return createNotationInfo(proof);
   }
   
   /**
    * Creates the {@link NotationInfo} for the given {@link Proof}.
    * @param proof The {@link Proof} to create its {@link NotationInfo}.
    * @return The created {@link NotationInfo}.
    */
   public static NotationInfo createNotationInfo(Proof proof) {
      NotationInfo notationInfo = new NotationInfo();
      if (proof != null && !proof.isDisposed()) {
         notationInfo.setAbbrevMap(proof.abbreviations());
      }
      return notationInfo;
   }
}
