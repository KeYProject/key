package de.uka.ilkd.key.symbolic_execution;

import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.PredicateTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Provides functionality to evaluate the truth value of labeled predicates.
 * @author Martin Hentschel
 */
public final class PredicateEvaluationUtil {
   /**
    * Forbid instances.
    */
   private PredicateEvaluationUtil() {
   }
   
   /**
    * Checks if the given {@link SequentFormula} is a predicate.
    * @param sequentFormula The {@link SequentFormula} to check.
    * @return {@code true} is predicate, {@code false} is something else.
    */
   public static boolean isPredicate(SequentFormula sequentFormula) {
      return sequentFormula != null ? 
             isPredicate(sequentFormula.formula()) : 
             false;
   }
   
   /**
    * Checks if the given {@link Term} is a predicate.
    * @param term The {@link Term} to check.
    * @return {@code true} is predicate, {@code false} is something else.
    */
   public static boolean isPredicate(Term term) {
      return term != null ? 
             isPredicate(term.op()) : 
             false;
   }
   
   /**
    * Checks if the given {@link Operator} is a predicate.
    * @param operator The {@link Operator} to check.
    * @return {@code true} is predicate, {@code false} is something else.
    */
   public static boolean isPredicate(Operator operator) {
      if (operator == Equality.EQV) {
         return false;
      }
      else if (operator instanceof Junctor) {
         return operator == Junctor.TRUE || operator == Junctor.FALSE;
      }
      else if (operator == AbstractTermTransformer.META_EQ ||
               operator == AbstractTermTransformer.META_GEQ ||
               operator == AbstractTermTransformer.META_GREATER ||
               operator == AbstractTermTransformer.META_LEQ ||
               operator == AbstractTermTransformer.META_LESS) {
         return true; // These Meta constructs evaluate always to true or false
      }
      else if (operator instanceof SortedOperator) {
         return ((SortedOperator) operator).sort() == Sort.FORMULA;
      }
      else {
         return false;
      }
   }
   
   /**
    * Checks if the given {@link Operator} is a {@link Junctor}.
    * @param operator The {@link Operator} to check.
    * @return {@code true} is {@link Junctor}, {@code false} is something else.
    */
   public static boolean isLogicOperator(Operator operator) {
      // TODO: Support <=> and quantors
      if (operator instanceof Junctor) {
         return operator != Junctor.TRUE && operator != Junctor.FALSE;
      }
      else {
         return false;
      }
   }
   
   /**
    * Evaluates the truth values in the subtree of the given {@link Node}
    * for predicates labeled with the given {@link TermLabel} name.
    * @param node The {@link Node} to start evaluation at.
    * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @return The result.
    * @throws ProofInputException Occurred Exception
    */
   public static PredicateEvaluationResult evaluate(Node node, 
                                                    Name termLabelName,
                                                    boolean useUnicode,
                                                    boolean usePrettyPrinting) throws ProofInputException {
      PredicateEvaluationResult result = new PredicateEvaluationResult();
      Deque<Map<String, IPredicateInstruction>> evaluationStack = new LinkedList<Map<String, IPredicateInstruction>>();
      evaluationStack.addFirst(new HashMap<String, IPredicateInstruction>());
      evaluateNode(node, useUnicode, usePrettyPrinting, node, termLabelName, evaluationStack, result);
      return result;
   }

   /**
    * Utility method used by {@link #evaluate(Node, Name)} for recursive evaluation.
    * @param node The current {@link Node}.
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
    * @param evaluationStack The not empty stack with evaluation results.
    * @param result The {@link PredicateEvaluationResult} to fill with leaf nodes.
    * @throws ProofInputException Occurred Exception
    */
   private static void evaluateNode(final Node evaluationNode,
                                    final boolean useUnicode,
                                    final boolean usePrettyPrinting,
                                    final Node node, 
                                    final Name termLabelName, 
                                    final Deque<Map<String, IPredicateInstruction>> evaluationStack, 
                                    final PredicateEvaluationResult result) throws ProofInputException {
      // Create new stack entry
      final Map<String, IPredicateInstruction> currentResults = evaluationStack.getFirst();
      // Analyze applied rule
      boolean childrenAlreadyTreated = false;
      if (node.getAppliedRuleApp() instanceof TacletApp) {
         TacletApp tacletApp = (TacletApp) node.getAppliedRuleApp();
         PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
         if (pio != null) {
            Term term = pio.subTerm();
            if (term != null) {
               TermLabel label = term.getLabel(termLabelName);
               if (label instanceof PredicateTermLabel) {
                  Taclet taclet = ((TacletApp) tacletApp).taclet();
                  if (taclet.goalTemplates().size() >= 1) { // Not a closing taclet
                     childrenAlreadyTreated = true;
                     int i = 0;
                     for (TacletGoalTemplate tacletGoal : taclet.goalTemplates()) {
                        Map<String, IPredicateInstruction> childResults = new HashMap<String, IPredicateInstruction>(currentResults);
                        analyzeTacletGoal(node, node.child(i), tacletApp, tacletGoal, (PredicateTermLabel) label, childResults);
                        // Evaluate children with branch specific Taclet result
                        evaluationStack.addFirst(childResults);
                        evaluateNode(evaluationNode, useUnicode, usePrettyPrinting, node.child(i), termLabelName, evaluationStack, result);
                        evaluationStack.removeFirst();
                        i++;
                     }
                  }
                  else {
                     if (pio.isInAntec()) {
                        updatePredicateResult((PredicateTermLabel) label, new PredicateResult(PredicateValue.FALSE, node), currentResults);
                     }
                     else {
                        updatePredicateResult((PredicateTermLabel) label, new PredicateResult(PredicateValue.TRUE, node), currentResults);
                     }
                  }
               }
            }
         }
      }
      else if (node.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp) {
         OneStepSimplifierRuleApp app = (OneStepSimplifierRuleApp) node.getAppliedRuleApp();
         for (RuleApp protocolApp : app.getProtocol()) {
            if (protocolApp instanceof TacletApp && protocolApp.posInOccurrence() != null) {
               TermLabel label = protocolApp.posInOccurrence().subTerm().getLabel(termLabelName);
               if (label instanceof PredicateTermLabel) {
                  TacletApp tacletApp = (TacletApp) protocolApp;
                  Taclet taclet = tacletApp.taclet();
                  assert taclet.goalTemplates().size() == 1;
                  analyzeTacletGoal(node, null, tacletApp, taclet.goalTemplates().head(), (PredicateTermLabel) label, currentResults);
               }
            }
         }
      }
      // Analyze children
      int childCount = node.childrenCount();
      if (childCount == 0) {
         Term condition = SymbolicExecutionUtil.computePathCondition(evaluationNode, node, true);
         String conditionString = SymbolicExecutionUtil.formatTerm(condition, node.proof().getServices(), useUnicode, usePrettyPrinting);
         result.addBranchResult(new BranchResult(node, currentResults, condition, conditionString, termLabelName));
      }
      else if (!childrenAlreadyTreated) {
         // Evaluate children in case that branch specific Taclet results are not available and thus not evaluated yet.
         for (int i = 0; i < childCount; i++) {
            evaluationStack.addFirst(new HashMap<String, IPredicateInstruction>(currentResults));
            evaluateNode(evaluationNode, useUnicode, usePrettyPrinting, node.child(i), termLabelName, evaluationStack, result);
            evaluationStack.removeFirst();
         }
      }
   }
   
   /**
    * Analyzes the given {@link TacletGoalTemplate}.
    * @param parent The current {@link Node} on which the rule was applied.
    * @param child The child node created by the given {@link TacletApp}.
    * @param tacletApp The {@link TacletApp}.
    * @param tacletGoal The {@link TacletGoalTemplate}.
    * @param label The {@link PredicateTermLabel}.
    * @param results The {@link Map} with all available {@link PredicateResult}s.
    */
   private static void analyzeTacletGoal(Node parent, 
                                         Node child,
                                         TacletApp tacletApp, 
                                         TacletGoalTemplate tacletGoal, 
                                         PredicateTermLabel label, 
                                         Map<String, IPredicateInstruction> results) {
      boolean truthValueEvaluationRequired = true;
      if (child != null) {
         Term replacement = checkForNewMinorIds(child.sequent(), label, tacletApp.posInOccurrence().isInAntec(), child.proof().getServices().getTermBuilder());
         if (replacement != null) {
            updatePredicateResult(label, new TermPredicateInstruction(replacement), results);
            truthValueEvaluationRequired = false;
         }
      }
      if (truthValueEvaluationRequired) {
         Object replaceObject = tacletGoal.replaceWithExpressionAsObject();
         if (replaceObject instanceof Term) {
            Term replaceTerm = SymbolicExecutionUtil.instantiateTerm((Term) replaceObject, tacletApp, parent.proof().getServices());
            // Check for true/false terms
            if (replaceTerm.op() == Junctor.TRUE) {
               updatePredicateResult(label, new PredicateResult(PredicateValue.TRUE, parent), results);
            }
            else if (replaceTerm.op() == Junctor.FALSE) {
               updatePredicateResult(label, new PredicateResult(PredicateValue.FALSE, parent), results);
            }
         }
      }
   }

   protected static Term checkForNewMinorIds(Sequent sequent, 
                                             PredicateTermLabel label,
                                             boolean antecedentRuleApplication,
                                             TermBuilder tb) {
      List<Term> antecedentReplacements = new LinkedList<Term>();
      List<Term> succedentReplacements = new LinkedList<Term>();
      for (SequentFormula sf : sequent.antecedent()) {
         findLabelReplacements(sf, label.name(), label.getId(), antecedentReplacements);
      }
      for (SequentFormula sf : sequent.succedent()) {
         findLabelReplacements(sf, label.name(), label.getId(), succedentReplacements);
      }
      if (!antecedentReplacements.isEmpty() && !succedentReplacements.isEmpty()) {
//         Term left = tb.and(antecedentReplacements);
//         Term right = tb.or(succedentReplacements);
//         if (antecedentRuleApplication) {
//            return tb.and(left, tb.not(right));
//         }
//         else {
//            return tb.and(tb.not(left), right);
//         }
         throw new UnsupportedOperationException();
      }
      else if (!antecedentReplacements.isEmpty()) {
         Term left = tb.and(antecedentReplacements);
         if (antecedentRuleApplication) {
            return left;
         }
         else {
            return tb.not(left);
         }
      }
      else if (!succedentReplacements.isEmpty()) {
         Term right = tb.or(succedentReplacements);
         if (!antecedentRuleApplication) {
            return right;
         }
         else {
            return tb.not(right);
         }
      }
      else {
         return null;
      }
   }
   
   protected static void findLabelReplacements(final SequentFormula sf, 
                                               final Name labelName,
                                               final String labelId, 
                                               final List<Term> resultToFill) {
      sf.formula().execPreOrder(new DefaultVisitor() {
         @Override
         public void visit(Term visited) {
            TermLabel visitedLabel = visited.getLabel(labelName);
            if (visitedLabel instanceof PredicateTermLabel) {
               PredicateTermLabel pLabel = (PredicateTermLabel) visitedLabel;
               if (JavaUtil.equals(pLabel.getBeforeId(), labelId)) {
                  resultToFill.add(visited);
               }
            }
         }
      });
   }

   /**
    * Updates the {@link IPredicateInstruction} of the given {@link TermLabel}.
    * @param label The {@link PredicateTermLabel} to update its {@link IPredicateInstruction}.
    * @param result The new {@link IPredicateInstruction}.
    * @param results The {@link Map} with all available {@link IPredicateInstruction}s.
    */
   private static void updatePredicateResult(PredicateTermLabel label, IPredicateInstruction result, Map<String, IPredicateInstruction> results) {
      results.put(label.getId(), result);
   }
   
   /**
    * Represents the final predicate evaluation result returned by
    * {@link PredicateEvaluationUtil#evaluateNode(Node, Name, Deque, PredicateEvaluationResult)}.
    * @author Martin Hentschel
    */
   public static class PredicateEvaluationResult {
      /**
       * The {@link BranchResult}s.
       */
      private final List<BranchResult> branchResults = new LinkedList<BranchResult>();
      
      /**
       * Adds a {@link BranchResult}.
       * @param result The {@link BranchResult} to add.
       */
      public void addBranchResult(BranchResult result) {
         if (result != null) {
            branchResults.add(result);            
         }
      }

      /**
       * Returns all {@link BranchResult}s.
       * @return The {@link BranchResult}s.
       */
      public BranchResult[] getBranchResults() {
         return branchResults.toArray(new BranchResult[branchResults.size()]);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         StringBuffer sb = new StringBuffer();
         boolean afterFirst = false;
         for (BranchResult result : branchResults) {
            if (afterFirst) {
               sb.append("\n\n");
            }
            else {
               afterFirst = true;
            }
            sb.append(result);
         }
         return sb.toString();
      }
   }
   
   /**
    * Represents the unmodifiable predicate results of a leaf {@link Node} ({@link Goal}).
    * @author Martin Hentschel
    */
   public static class BranchResult {
      /**
       * All predicate results.
       */
      private final Map<String, IPredicateInstruction> results;
      
      /**
       * The leaf {@link Node}.
       */
      private final Node leafNode;
      
      /**
       * The condition under which the leaf {@link Node} is reached from the analyzed {@link Node}.
       */
      private final Term condition;
      
      /**
       * The human readable condition under which the leaf {@link Node} is reached from the analyzed {@link Node}.
       */
      private final String conditionString;
      
      /**
       * The {@link Name} of the {@link TermLabel} to consider.
       */
      private final Name termLabelName;
      
      /**
       * Constructor. 
       * @param leafNode The leaf {@link Node}.
       * @param results All predicate results.
       * @param condition The condition under which the leaf {@link Node} is reached from the analyzed {@link Node}.
       * @param conditionString The human readable condition under which the leaf {@link Node} is reached from the analyzed {@link Node}.
       * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
       */
      public BranchResult(Node leafNode, 
                          Map<String, IPredicateInstruction> results,
                          Term condition,
                          String conditionString,
                          Name termLabelName) {
         assert leafNode != null;
         assert results != null;
         assert termLabelName != null;
         this.leafNode = leafNode;
         this.results = results;
         this.condition = condition;
         this.conditionString = conditionString;
         this.termLabelName = termLabelName;
      }

      /**
       * Returns all predicate results.
       * @return All predicate results.
       */
      public Map<String, IPredicateInstruction> getResults() {
         return Collections.unmodifiableMap(results);
      }
      
      /**
       * Returns the {@link PredicateResult} for the given {@link PredicateTermLabel}.
       * @param termLabel The {@link PredicateTermLabel}.
       * @return The found {@link PredicateResult} or {@code null} if not available.
       */
      public IPredicateInstruction getResult(PredicateTermLabel termLabel) {
         return termLabel != null ? results.get(termLabel.getId()) : null;
      }
      
      /**
       * Returns the condition under which the leaf {@link Node} is reached from the analyzed {@link Node}.
       * @return The condition under which the leaf {@link Node} is reached from the analyzed {@link Node}.
       */
      public Term getCondition() {
         return condition;
      }

      /**
       * Returns the human readable condition under which the leaf {@link Node} is reached from the analyzed {@link Node}.
       * @return The human readable condition under which the leaf {@link Node} is reached from the analyzed {@link Node}.
       */
      public String getConditionString() {
         return conditionString;
      }
      
      /**
       * Returns the {@link Name} of the {@link TermLabel} to consider.
       * @return The {@link Name} of the {@link TermLabel} to consider.
       */
      public Name getTermLabelName() {
         return termLabelName;
      }
      
      /**
       * Checks if the {@link Term} has a {@link TermLabel} with {@link Name} {@link #getTermLabelName()}.
       * @param term The {@link Term} to check.
       * @return {@code true} has {@link TermLabel}, {@code false} do not has {@link TermLabel}.
       */
      public boolean hasPredicateLabel(Term term) {
         return getPredicateLabel(term) != null;
      }

      /**
       * Returns the first {@link PredicateTermLabel} with {@link Name} {@link #getTermLabelName()}.
       * @param term The {@link Term}.
       * @return The found {@link PredicateTermLabel} or {@code null} otherwise.
       */
      public PredicateTermLabel getPredicateLabel(Term term) {
         TermLabel label = term.getLabel(termLabelName);
         return label instanceof PredicateTermLabel ? (PredicateTermLabel) label : null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         StringBuffer sb = new StringBuffer();
         sb.append("Goal ");
         sb.append(leafNode.serialNr());
         sb.append("\n");
         boolean afterFirst = false;
         for (Entry<String, IPredicateInstruction> entry : results.entrySet()) {
            if (afterFirst) {
               sb.append("\n");
            }
            else {
               afterFirst = true;
            }
            sb.append(entry.getKey());
            sb.append(" = ");
            sb.append(entry.getValue().evaluate(termLabelName, results));
            sb.append(" :: ");
            sb.append(entry.getValue());
         }
         return sb.toString();
      }

      /**
       * Evaluates the given {@link PredicateTermLabel}.
       * @param termLabel The {@link PredicateTermLabel} to evaluate.
       * @return The evaluation result.
       */
      public PredicateResult evaluate(PredicateTermLabel termLabel) {
         if (termLabel != null) {
            IPredicateInstruction instruction = getResult(termLabel);
            return instruction != null ? instruction.evaluate(termLabelName, results) : null;
         }
         else {
            return null;
         }
      }
   }
   
   public static interface IPredicateInstruction {
      public PredicateResult evaluate(Name termLabelName, Map<String, IPredicateInstruction> results);
   }
   
   /**
    * Represents the truth value of a predicate.
    * <b>This class needs to be unmodifiable.</b>
    * @author Martin Hentschel
    */
   public static class PredicateResult implements IPredicateInstruction {
      /**
       * The truth value.
       */
      private final PredicateValue value;
      
      /**
       * The {@link Node}s on which the truth value is based on.
       */
      private final Set<Node> nodes = new LinkedHashSet<Node>();

      /**
       * Constructor.
       * @param value The truth value.
       * @param nodes The {@link Node}s on which the truth value is based on.
       */
      public PredicateResult(PredicateValue value, Node... nodes) {
         assert value != null;
         this.value = value;
         JavaUtil.addAll(this.nodes, nodes);
      }

      /**
       * Constructor.
       * @param value The truth value.
       * @param nodes The {@link Node}s on which the truth value is based on.
       */
      public PredicateResult(PredicateValue value, Node[]... nodes) {
         assert value != null;
         this.value = value;
         for (Node[] currentNodes : nodes) {
            JavaUtil.addAll(this.nodes, currentNodes);
         }
      }

      /**
       * Returns the truth value.
       * @return The truth value.
       */
      public PredicateValue getValue() {
         return value;
      }
      
      /**
       * Returns the {@link Node}s on which the truth value is based on.
       * @return The {@link Node}s on which the truth value is based on.
       */
      public Node[] getNodes() {
         return nodes.toArray(new Node[nodes.size()]);
      }

      /**
       * {@inheritDoc}
       * @return
       */
      @Override
      public String toString() {
         StringBuffer sb = new StringBuffer();
         sb.append(value);
         if (!nodes.isEmpty()) {
            sb.append(" based on nodes ");
            boolean afterFirst = false;
            for (Node node : nodes) {
               if (afterFirst) {
                  sb.append(", ");
               }
               else {
                  afterFirst = true;
               }
               sb.append(node.serialNr());
            }
         }
         return sb.toString();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public PredicateResult evaluate(Name termLabelName, Map<String, IPredicateInstruction> results) {
         return this;
      }
   }
   
   public static class TermPredicateInstruction implements IPredicateInstruction {
      private final Term term;

      public TermPredicateInstruction(Term term) {
         assert term != null;
         this.term = term;
      }

      @Override
      public String toString() {
         return term.toString();
      }

      @Override
      public PredicateResult evaluate(Name termLabelName, Map<String, IPredicateInstruction> results) {
         TermLabel label = term.getLabel(termLabelName);
         // Return direct label result if available
         if (label instanceof PredicateTermLabel) {
            IPredicateInstruction instruction = results.get(((PredicateTermLabel) label).getId());
            if (instruction != null) {
               return instruction.evaluate(termLabelName, results);
            }
         }
         // If direct label result is not available try to compute it. (e.g. because of or/and label was replaced by sequent top level formuals)
         if (term.op() == Junctor.AND ||
             term.op() == Junctor.IMP ||
             term.op() == Junctor.OR) {
            Term leftTerm = term.sub(0);
            Term rightTerm = term.sub(1);
            TermLabel leftLabel = leftTerm.getLabel(termLabelName);
            TermLabel rightLabel = rightTerm.getLabel(termLabelName);
            IPredicateInstruction leftInstruction = leftLabel instanceof PredicateTermLabel ? results.get(((PredicateTermLabel) leftLabel).getId()) : null;
            IPredicateInstruction rightInstruction = rightLabel instanceof PredicateTermLabel ? results.get(((PredicateTermLabel) rightLabel).getId()) : null;
            PredicateResult leftResult = leftInstruction != null ? leftInstruction.evaluate(termLabelName, results) : null;
            PredicateResult rightResult = rightInstruction != null ? rightInstruction.evaluate(termLabelName, results) : null;
            PredicateValue leftValue = leftResult != null ? leftResult.getValue() : null;
            PredicateValue rightValue = rightResult != null ? rightResult.getValue() : null;
            PredicateValue resultValue;
            if (term.op() == Junctor.AND) {
               resultValue = PredicateValue.and(leftValue, rightValue);
            }
            else if (term.op() == Junctor.IMP) {
               resultValue = PredicateValue.imp(leftValue, rightValue);
            }
            else if (term.op() == Junctor.OR) {
               resultValue = PredicateValue.or(leftValue, rightValue);
            }
            else {
               throw new IllegalStateException("Operator '" + term.op() + "' is not supported.");
            }
            return new PredicateResult(resultValue, 
                                       leftResult != null ? leftResult.getNodes() : null,
                                       rightResult != null ? rightResult.getNodes() : null);
         }
         else if (term.op() == Junctor.NOT) {
            Term argumentTerm = term.sub(0);
            TermLabel argumentLabel = argumentTerm.getLabel(termLabelName);
            IPredicateInstruction argumentInstruction = argumentLabel instanceof PredicateTermLabel ? results.get(((PredicateTermLabel) argumentLabel).getId()) : null;
            PredicateResult argumentResult = argumentInstruction != null ? argumentInstruction.evaluate(termLabelName, results) : null;
            PredicateValue argumentValue = argumentResult != null ? argumentResult.getValue() : null;
            PredicateValue resultValue = PredicateValue.not(argumentValue);
            return new PredicateResult(resultValue, 
                                       argumentResult != null ? argumentResult.getNodes() : null);
         }
         else {
            return null;
         }
      }
   }
   
   /**
    * Represents the possible truth values.
    * @author Martin Hentschel
    */
   public static enum PredicateValue {
      /**
       * True.
       */
      TRUE,
      
      /**
       * False.
       */
      FALSE,
      
      /**
       * Unknown in cases:
       * <ul>
       *    <li>Predicate evaluates to true and false.</li>
       *    <li>Predicate is dropped without evaluation.</li>
       *    <li>Predicate is never evaluated.</li>
       * </ul>
       */
      UNKNOWN;

      /**
       * {@inheritDoc}
       * @return
       */
      @Override
      public String toString() {
         if (this == TRUE) {
            return "true";
         }
         else if (this == FALSE) {
            return "false";
         }
         else {
            return "unknown";
         }
      }

      /**
       * Computes the {@code and} value.
       * @param left The left {@link PredicateValue}.
       * @param right The right {@link PredicateValue}.
       * @return The computed {@code and} value.
       */
      public static PredicateValue and(PredicateValue left, PredicateValue right) {
         if (left == null || UNKNOWN.equals(left)) {
            if (FALSE.equals(right)) {
               return FALSE;
            }
            else {
               return UNKNOWN;
            }
         }
         else if (right == null || UNKNOWN.equals(right)) {
            if (FALSE.equals(left)) {
               return FALSE;
            }
            else {
               return UNKNOWN;
            }
         }
         else {
            if (TRUE.equals(left) && TRUE.equals(right)) {
               return TRUE;
            }
            else {
               return FALSE;
            }
         }
      }

      /**
       * Computes the {@code imp} value.
       * @param left The left {@link PredicateValue}.
       * @param right The right {@link PredicateValue}.
       * @return The computed {@code imp} value.
       */
      public static PredicateValue imp(PredicateValue left, PredicateValue right) {
         return or(not(left), right);
      }

      /**
       * Computes the {@code or} value.
       * @param left The left {@link PredicateValue}.
       * @param right The right {@link PredicateValue}.
       * @return The computed {@code or} value.
       */
      public static PredicateValue or(PredicateValue left, PredicateValue right) {
         if (left == null || UNKNOWN.equals(left)) {
            if (TRUE.equals(right)) {
               return TRUE;
            }
            else {
               return UNKNOWN;
            }
         }
         else if (right == null || UNKNOWN.equals(right)) {
            if (TRUE.equals(left)) {
               return TRUE;
            }
            else {
               return UNKNOWN;
            }
         }
         else {
            if (TRUE.equals(left) || TRUE.equals(right)) {
               return TRUE;
            }
            else {
               return FALSE;
            }
         }
      }

      /**
       * Computes the {@code not} value.
       * @param value The {@link PredicateValue}.
       * @return The computed {@code not} value.
       */
      public static PredicateValue not(PredicateValue value) {
         if (TRUE.equals(value)) {
            return FALSE;
         }
         else if (FALSE.equals(value)) {
            return TRUE;
         }
         else {
            return UNKNOWN;
         }
      }
   }
}
