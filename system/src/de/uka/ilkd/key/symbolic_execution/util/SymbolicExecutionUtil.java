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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
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
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
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
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionElement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionVariable;
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
      ApplyStrategyInfo info = SideProofUtil.startSideProof(parentProof, sequentToProve, true);
      try {
         // The simplified formula is the conjunction of all open goals
         ImmutableList<Goal> openGoals = info.getProof().openEnabledGoals();
         final TermBuilder tb = parentProof.getServices().getTermBuilder();
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
         SideProofUtil.disposeOrStore("Simplification of " + ProofSaver.printAnything(term, parentProof.getServices()), info);
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
      Function newPredicate = new Function(new Name(services.getTermBuilder().newName("ResultPredicate")), Sort.FORMULA, variable.sort());
      // Create formula which contains the value interested in.
      Term newTerm = services.getTermBuilder().func(newPredicate, services.getTermBuilder().var((ProgramVariable)variable));
      // Create Sequent to prove with new succedent.
      Sequent sequentToProve = createSequentToProveWithNewSuccedent(node, additionalConditions, newTerm, false);
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
    * @param keepUpdates {@code true} keep updates, {@code false} throw updates away.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   public static SiteProofVariableValueInput createExtractTermSequent(Services services,
                                                                      Node node,
                                                                      Term additionalConditions,
                                                                      Term term,
                                                                      boolean keepUpdates) {
      // Make sure that correct parameters are given
      assert node != null;
      assert term != null;
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(services.getTermBuilder().newName("ResultPredicate")), Sort.FORMULA, term.sort());
      // Create formula which contains the value interested in.
      Term newTerm = services.getTermBuilder().func(newPredicate, term);
      // Create Sequent to prove with new succedent.
      Sequent sequentToProve = keepUpdates ? 
                               createSequentToProveWithNewSuccedent(node, additionalConditions, newTerm, false) :
                               createSequentToProveWithNewSuccedent(node, additionalConditions, newTerm, null, false);
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
    * Checks if it is right now possible to compute the variables of the given {@link IExecutionStateNode}
    * via {@link IExecutionStateNode#getVariables()}. 
    * @param node The {@link IExecutionStateNode} to check.
    * @param services The {@link Services} to use.
    * @return {@code true} right now it is possible to compute variables, {@code false} it is not possible to compute variables.
    * @throws ProofInputException Occurred Exception.
    */
   public static boolean canComputeVariables(IExecutionStateNode<?> node, Services services) throws ProofInputException {
      return node != null && 
             !node.isDisposed() &&
             !services.getTermBuilder().ff().equals(node.getPathCondition());
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
         if (callNode != null
                 && callNode.getNodeInfo().getActiveStatement() instanceof MethodBodyStatement) {
            MethodBodyStatement mbs =
                    (MethodBodyStatement)callNode.getNodeInfo().getActiveStatement();
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
   public static ProgramVariable getProgramVariable(Services services, HeapLDT heapLDT,
                                                    Term locationTerm) {
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
      Term term = node.getAppliedRuleApp().posInOccurrence().subTerm();
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
               return isNotImplicite(node.proof().getServices(), pm);
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
    * @return {@code true} is not implicite, {@code false} is implicite 
    */
   public static boolean isNotImplicite(Services services, IProgramMethod pm) {
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
      int stackSize = computeStackSize(ruleApp);
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
         if (isMethodCallNode(parent, parent.getAppliedRuleApp(),
                              parent.getNodeInfo().getActiveStatement(), true) &&
             computeStackSize(parent.getAppliedRuleApp()) < stackSize) {
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
            return isNotImplicite(node.proof().getServices(), target);
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
            return term.containsLabel(ParameterlessTermLabel.LOOP_BODY_LABEL);
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
         return term.containsLabel(ParameterlessTermLabel.LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL);
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
         return (SymbolicExecutionTermLabel)JavaUtil.search(term.getLabels(),
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
    * Searches the modality {@link Term} with the maximal {@link SymbolicExecutionTermLabel} ID
    * {@link SymbolicExecutionTermLabel#getId()} in the given {@link Sequent}.
    * @param sequent The {@link Sequent} to search in.
    * @return The modality {@link Term} with the maximal ID if available or {@code null} otherwise.
    */
   public static Term findModalityWithMaxSymbolicExecutionLabelId(Sequent sequent) {
      if (sequent != null) {
         Term nextAntecedent = findModalityWithMaxSymbolicExecutionLabelId(sequent.antecedent());
         Term nextSuccedent = findModalityWithMaxSymbolicExecutionLabelId(sequent.succedent());
         if (nextAntecedent != null) {
            if (nextSuccedent != null) {
               SymbolicExecutionTermLabel antecedentLabel = getSymbolicExecutionLabel(nextAntecedent);
               SymbolicExecutionTermLabel succedentLabel = getSymbolicExecutionLabel(nextSuccedent);
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
    * @return The modality {@link Term} with the maximal ID if available or {@code null} otherwise.
    */
   public static Term findModalityWithMaxSymbolicExecutionLabelId(Semisequent semisequent) {
      if (semisequent != null) {
         int maxId = Integer.MIN_VALUE;
         Term modality = null;
         for (SequentFormula sf : semisequent) {
            Term current = findModalityWithMaxSymbolicExecutionLabelId(sf.formula());
            if (current != null) {
               SymbolicExecutionTermLabel label = getSymbolicExecutionLabel(current);
               if (modality == null || label.getId() > maxId) {
                  modality = current;
                  maxId = label.getId();
               }
            }
         }
         return modality;
      }
      else {
         return null;
      }
   }

   /**
    * Searches the modality {@link Term} with the maximal {@link SymbolicExecutionTermLabel} ID
    * {@link SymbolicExecutionTermLabel#getId()} in the given {@link Term}.
    * @param term The {@link Term} to search in.
    * @return The modality {@link Term} with the maximal ID if available or {@code null} otherwise.
    */
   public static Term findModalityWithMaxSymbolicExecutionLabelId(Term term) {
      if (term != null) {
         FindModalityWithSymbolicExecutionLabelId visitor =
                 new FindModalityWithSymbolicExecutionLabelId(true);
         term.execPreOrder(visitor);
         return visitor.getModality();
      }
      else {
         return null;
      }
   }
   
   /**
    * Searches the modality {@link Term} with the minimal {@link SymbolicExecutionTermLabel} ID
    * {@link SymbolicExecutionTermLabel#getId()} in the given {@link Sequent}.
    * @param sequent The {@link Sequent} to search in.
    * @return The modality {@link Term} with the maximal ID if available or {@code null} otherwise.
    */
   public static Term findModalityWithMinSymbolicExecutionLabelId(Sequent sequent) {
      if (sequent != null) {
         Term nextAntecedent = findModalityWithMinSymbolicExecutionLabelId(sequent.antecedent());
         Term nextSuccedent = findModalityWithMinSymbolicExecutionLabelId(sequent.succedent());
         if (nextAntecedent != null) {
            if (nextSuccedent != null) {
               SymbolicExecutionTermLabel antecedentLabel = getSymbolicExecutionLabel(nextAntecedent);
               SymbolicExecutionTermLabel succedentLabel = getSymbolicExecutionLabel(nextSuccedent);
               return antecedentLabel.getId() < succedentLabel.getId() ?
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
    * Searches the modality {@link Term} with the minimal {@link SymbolicExecutionTermLabel} ID
    * {@link SymbolicExecutionTermLabel#getId()} in the given {@link Semisequent}.
    * @param semisequent The {@link Semisequent} to search in.
    * @return The modality {@link Term} with the minimal ID if available or {@code null} otherwise.
    */
   public static Term findModalityWithMinSymbolicExecutionLabelId(Semisequent semisequent) {
      if (semisequent != null) {
         int maxId = Integer.MIN_VALUE;
         Term modality = null;
         for (SequentFormula sf : semisequent) {
            Term current = findModalityWithMinSymbolicExecutionLabelId(sf.formula());
            if (current != null) {
               SymbolicExecutionTermLabel label = getSymbolicExecutionLabel(current);
               if (modality == null || label.getId() < maxId) {
                  modality = current;
                  maxId = label.getId();
               }
            }
         }
         return modality;
      }
      else {
         return null;
      }
   }

   /**
    * Searches the modality {@link Term} with the minimal {@link SymbolicExecutionTermLabel} ID
    * {@link SymbolicExecutionTermLabel#getId()} in the given {@link Term}.
    * @param term The {@link Term} to search in.
    * @return The modality {@link Term} with the maximal ID if available or {@code null} otherwise.
    */
   public static Term findModalityWithMinSymbolicExecutionLabelId(Term term) {
      if (term != null) {
         FindModalityWithSymbolicExecutionLabelId visitor =
                 new FindModalityWithSymbolicExecutionLabelId(false);
         term.execPreOrder(visitor);
         return visitor.getModality();
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
       * The modality {@link Term} with the maximal ID.
       */
      private Term modality;
      
      /**
       * The maximal ID.
       */
      private int maxId;
      
      /**
       * {@code true} search maximal ID, {@code false} search minimal ID.
       */
      private boolean maximum;
      
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
            if (modality == null || (maximum ? label.getId() > maxId : label.getId() < maxId)) {
               modality = visited;
               maxId = label.getId();
            }
         }
      }

      /**
       * Returns the modality {@link Term} with the maximal ID.
       * @return The modality {@link Term} with the maximal ID.
       */
      public Term getModality() {
         return modality;
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
         else if (isLoopStatement(node, ruleApp, statement, posInfo)) { 
            return isFirstLoopIteration(node, ruleApp, statement);
         }
         else if (isBranchStatement(node, ruleApp, statement, posInfo) ||
                  isMethodCallNode(node, ruleApp, statement) ||
                  isStatementNode(node, ruleApp, statement, posInfo) ||
                  isTerminationNode(node, ruleApp)) {
            return true;
         }
         else if (hasLoopCondition(node, ruleApp, statement)) {
            return ((LoopStatement)statement).getGuardExpression().getPositionInfo()
                        != PositionInfo.UNDEFINED &&
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
    * @return The parent {@link Node} of the given {@link Node} which is also a set node or {@code null} if no parent node was found.
    */
   public static Node findMethodCallNode(Node node) {
      if (node != null && node.getAppliedRuleApp() != null) {
         // Get current program method
         Term term = node.getAppliedRuleApp().posInOccurrence().subTerm();
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
                   ((MethodBodyStatement)activeStatement).getProgramMethod(services)
                       == mf.getProgramMethod()) {
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
    * @param improveReadability {@code true} improve readability, {@code false} do not improve readability.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term computeBranchCondition(Node node,
                                             boolean improveReadability) throws ProofInputException {
      // Get applied taclet on parent proof node
      Node parent = node.parent();
      if (parent.getAppliedRuleApp() instanceof TacletApp) {
         return computeTacletAppBranchCondition(parent, node, improveReadability);
      }
      else if (parent.getAppliedRuleApp() instanceof ContractRuleApp) {
        return computeContractRuleAppBranchCondition(parent, node, improveReadability);
      }
      else if (parent.getAppliedRuleApp() instanceof LoopInvariantBuiltInRuleApp) {
         return computeLoopInvariantBuiltInRuleAppBranchCondition(parent, node, improveReadability);
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
    * @param improveReadability {@code true} improve readability, {@code false} do not improve readability.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   private static Term computeContractRuleAppBranchCondition(Node parent,
                                                             Node node,
                                                             boolean improveReadability) throws ProofInputException {
      final Services services = node.proof().getServices();
      // Make sure that a computation is possible
      if (!(parent.getAppliedRuleApp() instanceof ContractRuleApp)) {
         throw new ProofInputException("Only ContractRuleApp is allowed in branch computation but rule \"" + parent.getAppliedRuleApp() + "\" was found.");
      }
      int childIndex = JavaUtil.indexOf(parent.childrenIterator(), node);
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
         // Collect all implications for normal or exceptional preconditions
         Term result;
         Term implications = search.getWorkingTerm().sub(1);
         ImmutableList<Term> implicationTerms = collectPreconditionImpliesPostconditionTerms(ImmutableSLList.<Term>nil(),
                                                                                             search.getExceptionDefinition(),
                                                                                             childIndex == 1, 
                                                                                             implications);
         if (!implicationTerms.isEmpty()) {
            // Implications find, return their conditions as branch condition
            ImmutableList<Term> condtionTerms = ImmutableSLList.<Term>nil();
            for (Term implication : implicationTerms) {
               condtionTerms = condtionTerms.append(implication.sub(0));
            }
            result = services.getTermBuilder().or(condtionTerms);
            // Add updates
            result = services.getTermBuilder().applyParallel(search.getUpdatesAndTerm().first, result);
         }
         else {
            // No preconditions available, branch condition is true
            result = services.getTermBuilder().tt();
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
         Sequent newSequent = createSequentToProveWithNewSuccedent(parent, (Term)null, result, true);
         Term condition = evaluateInSideProof(services, 
                                              parent.proof(), 
                                              newSequent, 
                                              ParameterlessTermLabel.RESULT_LABEL, 
                                              "Operation contract branch condition computation on node " + parent.serialNr() + " for branch " + node.serialNr() + ".",
                                              StrategyProperties.SPLITTING_OFF);
         if (improveReadability) {
            condition = improveReadability(condition, services);
         }
         return condition;
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
      if (workingTerm.op() != Junctor.AND) {
         throw new ProofInputException("And operation expected, implementation of UseOperationContractRule might has changed!"); 
      }
      // Find Term exc_n = null which is added (maybe negated) to all exceptional preconditions
      Term exceptionDefinitionParent = null;
      Term exceptionDefinition = workingTerm;
      while (exceptionDefinition.op() == Junctor.AND) {
         exceptionDefinitionParent = exceptionDefinition;
         Term firstSub = exceptionDefinition.sub(0);
//         if (firstSub.op() == Junctor.NOT) {
//            firstSub = firstSub.sub(0);
//         }
//         if (firstSub.op() == Equality.EQUALS && 
//             isNullSort(firstSub.sub(1).sort(), services) &&
//             services.getJavaInfo().isSubtype(services.getJavaInfo().getKeYJavaType(firstSub.sub(0).sort()), services.getJavaInfo().getKeYJavaType("java.lang.Throwable"))) {
//            exceptionDefinition = exceptionDefinition.sub(0);
//         }
//         else {
//            exceptionDefinition = exceptionDefinition.sub(1);
//         }
         if (firstSub.op() == node.proof().getServices().getJavaInfo().getInv()) { 
            exceptionDefinition = exceptionDefinition.sub(1);
         }
         else {
            if (firstSub.op() == Equality.EQUALS && 
                (!isNullSort(firstSub.sub(1).sort(), services) ||
                !services.getJavaInfo().isSubtype(services.getJavaInfo().getKeYJavaType(firstSub.sub(0).sort()), services.getJavaInfo().getKeYJavaType("java.lang.Throwable")))) {
               exceptionDefinition = exceptionDefinition.sub(1);
            }
            else {
               exceptionDefinition = firstSub;//exceptionDefinition.sub(exceptionDefinition.arity() - 1);
            }
         }
      }
      // Make sure that exception equality was found
      Term exceptionEquality;
      if (exceptionDefinition.op() == Junctor.NOT) {
         exceptionEquality = exceptionDefinition.sub(0);
      }
      else {
         exceptionEquality = exceptionDefinition;
      }
      if (exceptionEquality.op() != Equality.EQUALS || exceptionEquality.arity() != 2) {
         throw new ProofInputException("Equality expected, implementation of UseOperationContractRule might has changed!"); 
      }
      if (!isNullSort(exceptionEquality.sub(1).sort(), services)) {
         throw new ProofInputException("Null expected, implementation of UseOperationContractRule might has changed!"); 
      }
      KeYJavaType exceptionType = services.getJavaInfo().getKeYJavaType(exceptionEquality.sub(0).sort());
      if (!services.getJavaInfo().isSubtype(exceptionType, services.getJavaInfo().getKeYJavaType("java.lang.Throwable"))) {
         throw new ProofInputException("Throwable expected, implementation of UseOperationContractRule might has changed!"); 
      }
      return new ContractPostOrExcPostExceptionVariableResult(workingTerm, updatesAndTerm, exceptionDefinition, exceptionDefinitionParent, exceptionEquality);
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
       * The found parent of {@link #exceptionDefinition}.
       */
      private Term exceptionDefinitionParent;
      
      /**
       * The equality which contains the equality.
       */
      private Term exceptionEquality;
      
      /**
       * Constructor.
       * @param workingTerm The working {@link Term}.
       * @param updatesAndTerm The updates.
       * @param exceptionDefinition The exception definition.
       * @param exceptionDefinitionParent The found parent of the given exception definition.
       * @param exceptionEquality The equality which contains the equality.
       */
      public ContractPostOrExcPostExceptionVariableResult(Term workingTerm, 
                                                          Pair<ImmutableList<Term>, Term> updatesAndTerm, 
                                                          Term exceptionDefinition,
                                                          Term exceptionDefinitionParent,
                                                          Term exceptionEquality) {
         this.workingTerm = workingTerm;
         this.updatesAndTerm = updatesAndTerm;
         this.exceptionDefinition = exceptionDefinition;
         this.exceptionDefinitionParent = exceptionDefinitionParent;
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
       * Returns the found parent of {@link #getExceptionDefinition()}.
       * @return The found parent of {@link #getExceptionDefinition()}.
       */
      public Term getExceptionDefinitionParent() {
         return exceptionDefinitionParent;
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
    * @param improveReadability {@code true} improve readability, {@code false} do not improve readability.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   private static Term computeLoopInvariantBuiltInRuleAppBranchCondition(Node parent,
                                                                         Node node,
                                                                         boolean improveReadability)
                                                                         throws ProofInputException {
      // Make sure that a computation is possible
      if (!(parent.getAppliedRuleApp() instanceof LoopInvariantBuiltInRuleApp)) {
         throw new ProofInputException("Only LoopInvariantBuiltInRuleApp is allowed in branch computation but rule \"" + parent.getAppliedRuleApp() + "\" was found.");
      }
      // Make sure that branch is supported
      int childIndex = JavaUtil.indexOf(parent.childrenIterator(), node);
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
             loopConditionModalityTerm.sub(0).sub(1) != (childIndex == 1 ? services.getTermBuilder().TRUE() : services.getTermBuilder().FALSE())) {
            throw new ProofInputException("Implementation of WhileInvariantRule has changed."); 
         }
         // Create formula which contains the value interested in.
         invTerm = TermBuilder.goBelowUpdates(invTerm);
         Term loopCondAndInv = services.getTermBuilder().and(loopConditionModalityTerm.sub(0), invTerm);
         Term newTerm = loopCondAndInv;
         Term modalityTerm = childIndex == 1 ?
                             services.getTermBuilder().box(loopConditionModalityTerm.javaBlock(), newTerm) :
                             services.getTermBuilder().dia(loopConditionModalityTerm.javaBlock(), newTerm);
         Sequent newSequent = createSequentToProveWithNewSuccedent(parent, (Term)null, modalityTerm, pair.first, true);
         Term condition = evaluateInSideProof(services, 
                                              parent.proof(), 
                                              newSequent, 
                                              ParameterlessTermLabel.RESULT_LABEL, 
                                              "Loop invariant branch condition computation on node " + parent.serialNr() + " for branch " + node.serialNr() + ".",
                                              StrategyProperties.SPLITTING_OFF);
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
    * Lists recursive implications filtered for post or exceptional post branch.
    * @param toFill The result {@link ImmutableList} to fill.
    * @param exceptionDefinition The exception definition {@code exc_0 = null}.
    * @param exceptionalExecution {@code true} exceptional post branch, {@code false} post branch.
    * @param root The root {@link Term} to start search in.
    * @return The found implications.
    */
   private static ImmutableList<Term>
                   collectPreconditionImpliesPostconditionTerms(ImmutableList<Term> toFill,
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
            // Collect only exceptional terms
            if (isExceptionCondition) {
               toFill = toFill.append(root);
            }
         }
         else {
            // Collect only normal terms
            if (!isExceptionCondition) {
               toFill = toFill.append(root);
            }
         }
      }
      else {
         for (Term sub : root.subs()) {
            toFill = collectPreconditionImpliesPostconditionTerms(toFill, exceptionDefinition,
                                                                  exceptionalExecution, sub);
         }
      }
      return toFill;
   }

   /**
    * Computes the branch condition of the given {@link Node} which was constructed by a {@link TacletApp}.
    * @param parent The parent {@link Node} of the given one.
    * @param node The {@link Node} to compute its branch condition.
    * @param improveReadability {@code true} improve readability, {@code false} do not improve readability.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   private static Term computeTacletAppBranchCondition(Node parent,
                                                       Node node,
                                                       boolean improveReadability) throws ProofInputException {
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
               newAntecedents = newAntecedents.append(services.getTermBuilder().applyUpdatePairsSequential(app.instantiations().getUpdateContext(), a));
            }
            // Apply updates on succedents and add result to new succedents list
            for (Term suc : succedents) {
               newSuccedents = newSuccedents.append(services.getTermBuilder().applyUpdatePairsSequential(app.instantiations().getUpdateContext(), suc));
            }
            // Add additional equivalenz term to antecedent with the replace object which must be equal to the find term 
            Term replaceTerm = (Term)goalTemplate.replaceWithExpressionAsObject();
            replaceTerm = services.getTermBuilder().equals(replaceTerm, app.posInOccurrence().subTerm());
            replaceTerm = services.getTermBuilder().applyUpdatePairsSequential(app.instantiations().getUpdateContext(), replaceTerm);
            if (!newAntecedents.contains(replaceTerm)) {
               newAntecedents = newAntecedents.append(replaceTerm);
            }
            // Replace old with new lists
            antecedents = newAntecedents;
            succedents = newSuccedents;
         }
         else if (goalTemplate.replaceWithExpressionAsObject() != null) {
            throw new ProofInputException("Expected replacement as Sequent or Term during branch condition computation but is \"" + goalTemplate.replaceWithExpressionAsObject() + "\".");
         }
      }
      // Construct branch condition from created antecedent and succedent terms as new implication 
      Term left = services.getTermBuilder().and(antecedents);
      Term right = services.getTermBuilder().or(succedents);
      Term leftAndRight = services.getTermBuilder().and(left, services.getTermBuilder().not(right));
      // Create formula which contains the value interested in.
      Sequent newSequent = createSequentToProveWithNewSuccedent(parent, (Term)null, leftAndRight, true);
      Term condition = evaluateInSideProof(services, 
                                           parent.proof(), 
                                           newSequent, 
                                           ParameterlessTermLabel.RESULT_LABEL, 
                                           "Taclet branch condition computation on node " + parent.serialNr() + " for branch " + node.serialNr() + ".",
                                           StrategyProperties.SPLITTING_OFF);
      if (improveReadability) {
         condition = improveReadability(condition, services);
      }
      return condition;
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
                                           Sequent sequentToProve, 
                                           TermLabel label, 
                                           String description, 
                                           String splittingOption) throws ProofInputException {
      List<Pair<Term, Node>> resultValuesAndConditions = SideProofUtil.computeResults(services, 
                                                                                      proof, 
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
         SyntacticalReplaceVisitor visitor = new SyntacticalReplaceVisitor(services, svInst, null, null);
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
      HashMap<String, String> clone = new LinkedHashMap<String, String>();
      clone.putAll(settings);
      clone.put(key, value);
      ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().setDefaultChoices(clone);
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
      Term isNull = services.getTermBuilder().equals(newSuccedent, services.getTermBuilder().NULL());
      Term isNotNull = services.getTermBuilder().not(isNull);
      Sequent sequentToProve = createSequentToProveWithNewSuccedent(node, additionalAntecedent, nullExpected ? isNull : isNotNull, false);
      // Execute proof in the current thread
      ApplyStrategyInfo info = SideProofUtil.startSideProof(node.proof(), 
                                                            sequentToProve, 
                                                            StrategyProperties.METHOD_CONTRACT,
                                                            StrategyProperties.LOOP_INVARIANT,
                                                            StrategyProperties.QUERY_ON,
                                                            StrategyProperties.SPLITTING_NORMAL,
                                                            true);
      try {
         return !info.getProof().openEnabledGoals().isEmpty();
      }
      finally {
         SideProofUtil.disposeOrStore("Null check on node " + node.serialNr() + ".", info);
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
                                                              RuleApp ruleApp,
                                                              Term newSuccedent) {
      return createSequentToProveWithNewSuccedent(node, ruleApp, null, newSuccedent, false);
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
      return createSequentToProveWithNewSuccedent(node, node.getAppliedRuleApp(), additionalAntecedent, newSuccedent, addResultLabel);
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
                                                              RuleApp ruleApp,
                                                              Term additionalAntecedent,
                                                              Term newSuccedent,
                                                              boolean addResultLabel) {
      if (ruleApp.posInOccurrence() != null) {
         // Get the updates from the return node which includes the value interested in.
         Term originalModifiedFormula = ruleApp.posInOccurrence().constrainedFormula().formula();
         ImmutableList<Term> originalUpdates = TermBuilder.goBelowUpdates2(originalModifiedFormula).first;
         // Create new sequent
         return createSequentToProveWithNewSuccedent(node, ruleApp, additionalAntecedent, newSuccedent, originalUpdates, addResultLabel);
      }
      else {
         return createSequentToProveWithNewSuccedent(node, ruleApp, additionalAntecedent, newSuccedent, null, addResultLabel);
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
      return createSequentToProveWithNewSuccedent(node, node.getAppliedRuleApp(), additionalAntecedent, newSuccedent, updates, addResultLabel);
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
                                                              RuleApp ruleApp,
                                                              Term additionalAntecedent,
                                                              Term newSuccedent,
                                                              ImmutableList<Term> updates,
                                                              boolean addResultLabel) {
      // Combine method frame, formula with value predicate and the updates which provides the values
      Term newSuccedentToProve;
      if (updates != null) {
         newSuccedentToProve = node.proof().getServices().getTermBuilder().applySequential(updates, newSuccedent);
      }
      else {
         newSuccedentToProve = newSuccedent;
      }
      // Create new sequent with the original antecedent and the formulas in the succedent which were not modified by the applied rule
      PosInOccurrence pio = ruleApp.posInOccurrence();
      Sequent originalSequentWithoutMethodFrame = SideProofUtil.computeGeneralSequentToProve(node.sequent(), pio != null ? pio.constrainedFormula() : null);
      Set<Term> skolemTerms = collectSkolemConstants(originalSequentWithoutMethodFrame, newSuccedentToProve);
      originalSequentWithoutMethodFrame = removeAllUnusedSkolemEqualities(originalSequentWithoutMethodFrame, skolemTerms);
      if (addResultLabel) {
         TermFactory factory = node.proof().getServices().getTermFactory();
         Set<Term> skolemInNewTerm = collectSkolemConstantsNonRecursive(newSuccedentToProve);
         originalSequentWithoutMethodFrame = labelSkolemConstants(originalSequentWithoutMethodFrame, skolemInNewTerm, factory);
         newSuccedentToProve = addLabelRecursiveToNonSkolem(factory, newSuccedentToProve, ParameterlessTermLabel.RESULT_LABEL);
      }
      Sequent sequentToProve = originalSequentWithoutMethodFrame.addFormula(new SequentFormula(newSuccedentToProve), false, true).sequent();
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
               Term definition = addLabelRecursiveToNonSkolem(factory, equality.sub(1), ParameterlessTermLabel.RESULT_LABEL);
               Term skolem = addLabelRecursiveToNonSkolem(factory, equality.sub(0), ParameterlessTermLabel.RESULT_LABEL);
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
               Term definition = addLabelRecursiveToNonSkolem(factory, equality.sub(0), ParameterlessTermLabel.RESULT_LABEL);
               Term skolem = addLabelRecursiveToNonSkolem(factory, equality.sub(1), ParameterlessTermLabel.RESULT_LABEL);
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
      // Collect skolem constants in term
      Set<Term> result = collectSkolemConstantsNonRecursive(term);
      // Collect all skolem constants used in skolem constants
      List<Term> toCheck = new LinkedList<Term>(result);
      while (!toCheck.isEmpty()) {
         Term skolemConstant = toCheck.remove(0);
         List<Term> replacements = findSkolemReplacements(sequent, skolemConstant);
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
         List<Term> replacements = findSkolemReplacements(sequent, term);
         assert !replacements.isEmpty();
         Term other = term.sub(1);
         List<Term> newTerms = new LinkedList<Term>();
         for (Term replacement : replacements) {
            newTerms.add(tb.equals(replacement, other));
         }
         term = tb.and(newTerms);
         return replaceSkolemConstants(sequent, term, services);
      }
      else if (skolemCheck == 1) {
         TermBuilder tb = services.getTermBuilder();
         List<Term> replacements = findSkolemReplacements(sequent, term);
         assert !replacements.isEmpty();
         Term other = term.sub(0);
         List<Term> newTerms = new LinkedList<Term>();
         for (Term replacement : replacements) {
            newTerms.add(tb.equals(other, replacement));
         }
         term = tb.and(newTerms);
         return replaceSkolemConstants(sequent, term, services);
      }
      else {
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
         return changed ? services.getTermFactory().createTerm(term.op(),
                                                               new ImmutableArray<Term>(newChildren),
                                                               term.boundVars(),
                                                               term.javaBlock(),
                                                               term.getLabels()) :
                          term;
      }
   }

   /**
    * Utility method of {@link #replaceSkolemConstants(Sequent, Term, Services)} to
    * find all equality parts of the given skolem constant.
    * @param sequent The {@link Sequent} which provides the skolem equalities.
    * @param skolemEquality The skolem equality to solve.
    * @return The equality parts of the given skolem equality.
    */
   private static List<Term> findSkolemReplacements(Sequent sequent, Term skolemEquality) {
      List<Term> result = new LinkedList<Term>();
      for (SequentFormula sf : sequent) {
         Term term = sf.formula();
         if (term != skolemEquality) {
            int skolemCheck = checkSkolemEquality(term);
            if (skolemCheck == -1) {
               result.add(term.sub(1));
            }
            else if (skolemCheck == 1) {
               result.add(term.sub(0));
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
      if (node != null) {
         final Services services = node.proof().getServices();
         Term pathCondition = services.getTermBuilder().tt();
         while (node != null) {
            Node parent = node.parent();
            if (parent != null && parent.childrenCount() >= 2) {
               Term branchCondition = computeBranchCondition(node, improveReadability);
               pathCondition = services.getTermBuilder().and(branchCondition, pathCondition);
            }
            node = parent;
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
      Term modalityTerm =
              SymbolicExecutionUtil.findModalityWithMinSymbolicExecutionLabelId(root.sequent());
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
      return !ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getChoices().isEmpty();
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
                    JavaUtil.search(simplifierApp.getProtocol(), new IFilter<RuleApp>() {
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
         return JavaUtil.search(heapLDT.getAllHeaps(), new IFilter<LocationVariable>() {
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
      String result = null;
      if (posInfo.getFileName() != null) {
         result = posInfo.getFileName(); // posInfo.getFileName() is a path to a file
      }
      else if (posInfo.getParentClass() != null) {
         result = posInfo.getParentClass(); // posInfo.getParentClass() is a path to a file
      }
      if (result != null && result.startsWith("FILE:")) {
         result = result.substring("FILE:".length());
      }
      return result;
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
      HashMap<String, String> result = new HashMap<String, String>();
      result.put("Strings", "Strings:on");
      result.put("reach", "reach:on");
      result.put("JavaCard", "JavaCard:off");
      result.put("assertions", "assertions:on");
      result.put("bigint", "bigint:on");
      result.put("intRules", "intRules:arithmeticSemanticsIgnoringOF");
      result.put("programRules", "programRules:Java");
      result.put("modelFields", "modelFields:showSatisfiability");
      result.put("initialisation", "initialisation:disableStaticInitialisation");
      result.put("sequences", "sequences:on");
      result.put("runtimeExceptions", "runtimeExceptions:allow");
      result.put("integerSimplificationRules", "integerSimplificationRules:full");
      result.put("optimisedSelectRules", "optimisedSelectRules:on");
      result.put("wdChecks", "wdChecks:off");
      result.put("wdOperator", "wdOperator:L");
      return result;
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
      return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
   }

   /**
    * Defines if pretty printing is enabled or not.
    * @param usePrettyPrinting {@code true} pretty printing is enabled, {@code false} pretty printing is disabled.
    */
   public static void setUsePrettyPrinting(boolean usePrettyPrinting) {
      ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(usePrettyPrinting);
      NotationInfo.PRETTY_SYNTAX = usePrettyPrinting;
   }

   /**
    * Checks if the {@link Goal} has applicable rules.
    * @param goal The {@link Goal} to check.
    * @return {@code true} has applicable rules, {@code false} no rules are applicable.
    */
   public static boolean hasApplicableRules(Goal goal) {
      return goal.getRuleAppManager().peekNext() != null;
   }
}
