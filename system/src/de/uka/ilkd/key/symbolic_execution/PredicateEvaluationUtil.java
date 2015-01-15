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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
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
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
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
    * Checks if the given {@link Term} is a logical operator
    * @param operator The {@link Term} to check.
    * @return {@code true} is logical operator, {@code false} is something else.
    */
   public static boolean isLogicOperator(Term term) {
      if (term != null) {
         return isLogicOperator(term.op(), term.subs());
      }
      else {
         return false;
      }
   }
   
   /**
    * Checks if the given {@link Operator} and its sub {@link Term}s specify a logical operator.
    * @param operator The {@link Operator}.
    * @param subs The sub {@link Term}s.
    * @return {@code true} is logical operator, {@code false} is something else.
    */
   public static boolean isLogicOperator(Operator operator, ImmutableArray<Term> subs) {
      // TODO: Quantors
      if (operator instanceof Junctor) {
         return operator != Junctor.TRUE && operator != Junctor.FALSE;
      }
      else if (operator == Equality.EQV) {
         return true;
      }
      else if (isIfThenElseFormula(operator, subs)) {
         return true;
      }
      else {
         return false;
      }
   }

   /**
    * Checks if the given {@link Term} is an if-then-else formula.
    * @param term The {@link Term} to check.
    * @return {@code true} is if-then-else formula, {@code false} is something else.
    */
   public static boolean isIfThenElseFormula(Term term) {
      if (term != null) {
         return isIfThenElseFormula(term.op(), term.subs());
      }
      else {
         return false;
      }
   }

   /**
    * Checks if the given {@link Operator} and its sub {@link Term}s specify an if-then-else formula.
    * @param operator The {@link Operator}.
    * @param subs The sub {@link Term}s.
    * @return {@code true} is if-then-else formula, {@code false} is something else.
    */
   public static boolean isIfThenElseFormula(Operator operator, ImmutableArray<Term> subs) {
      if (operator == IfThenElse.IF_THEN_ELSE) {
         Sort sort = operator.sort(subs);
         return sort == Sort.FORMULA;
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
      evaluateNode(node, useUnicode, usePrettyPrinting, node, termLabelName, evaluationStack, result, node.proof().getServices());
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
    * @param services The {@link Services} to use.
    * @throws ProofInputException Occurred Exception
    */
   private static void evaluateNode(final Node evaluationNode,
                                    final boolean useUnicode,
                                    final boolean usePrettyPrinting,
                                    final Node node, 
                                    final Name termLabelName, 
                                    final Deque<Map<String, IPredicateInstruction>> evaluationStack, 
                                    final PredicateEvaluationResult result,
                                    final Services services) throws ProofInputException {
      // Create new stack entry
      final Map<String, IPredicateInstruction> currentResults = evaluationStack.getFirst();
      // Check for new minor ids created by parent rule application
      updatePredicateResultBasedOnNewMinorIds(node, termLabelName, services.getTermBuilder(), currentResults);
      // Analyze applied rule
      boolean childrenAlreadyTreated = false;
      if (node.getAppliedRuleApp() instanceof TacletApp) {
         TacletApp tacletApp = (TacletApp) node.getAppliedRuleApp();
         List<PredicateLabelOccurrence> labels = findInvolvedLabels(node.sequent(), tacletApp, termLabelName);
         if (!labels.isEmpty()) {
            Taclet taclet = ((TacletApp) tacletApp).taclet();
            if (taclet.goalTemplates().size() >= 1) { // Not a closing taclet
               childrenAlreadyTreated = true;
               int i = 0;
               for (TacletGoalTemplate tacletGoal : taclet.goalTemplates().reverse()) {
                  Map<String, IPredicateInstruction> childResults = new HashMap<String, IPredicateInstruction>(currentResults);
                  analyzeTacletGoal(node, tacletApp, tacletGoal, labels, services, childResults);
                  // Evaluate children with branch specific Taclet result
                  evaluationStack.addFirst(childResults);
                  evaluateNode(evaluationNode, useUnicode, usePrettyPrinting, node.child(i), termLabelName, evaluationStack, result, services);
                  evaluationStack.removeFirst();
                  i++;
               }
            }
            else if (tacletApp.posInOccurrence() != null){
               for (PredicateLabelOccurrence occurrence : labels) {
                  PredicateResult newResult = new PredicateResult(occurrence.isInAntecedent() ? PredicateValue.FALSE : PredicateValue.TRUE, node);
                  updatePredicateResult(occurrence.getLabel(), newResult, currentResults);
               }
            }
         }
      }
      else if (node.getAppliedRuleApp() instanceof OneStepSimplifierRuleApp) {
         OneStepSimplifierRuleApp app = (OneStepSimplifierRuleApp) node.getAppliedRuleApp();
         for (RuleApp protocolApp : app.getProtocol()) {
            if (protocolApp instanceof TacletApp) {
               TacletApp tacletApp = (TacletApp) protocolApp;
               Taclet taclet = tacletApp.taclet();
               assert taclet.goalTemplates().size() == 1;
               List<PredicateLabelOccurrence> labels = findInvolvedLabels(node.sequent(), tacletApp, termLabelName);
               if (!labels.isEmpty()) {
                  analyzeTacletGoal(node, tacletApp, taclet.goalTemplates().head(), labels, services, currentResults);
               }
            }
         }
      }
      // Analyze children
      int childCount = node.childrenCount();
      if (childCount == 0) {
         Term condition = SymbolicExecutionUtil.computePathCondition(evaluationNode, node, false, true);
         String conditionString = SymbolicExecutionUtil.formatTerm(condition, services, useUnicode, usePrettyPrinting);
         result.addBranchResult(new BranchResult(node, currentResults, condition, conditionString, termLabelName));
      }
      else if (!childrenAlreadyTreated) {
         // Evaluate children in case that branch specific Taclet results are not available and thus not evaluated yet.
         for (int i = 0; i < childCount; i++) {
            evaluationStack.addFirst(new HashMap<String, IPredicateInstruction>(currentResults));
            evaluateNode(evaluationNode, useUnicode, usePrettyPrinting, node.child(i), termLabelName, evaluationStack, result, services);
            evaluationStack.removeFirst();
         }
      }
   }
   
   /**
    * Computes the occurrences of all involved {@link PredicateTermLabel}s.
    * @param sequent The {@link Sequent} on which the given {@link TacletApp} was applied.
    * @param tacletApp The applied {@link TacletApp}.
    * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
    * @return The found {@link PredicateLabelOccurrence}s.
    */
   private static List<PredicateLabelOccurrence> findInvolvedLabels(Sequent sequent, 
                                                                    TacletApp tacletApp, 
                                                                    Name termLabelName) {
      List<PredicateLabelOccurrence> result = new LinkedList<PredicateLabelOccurrence>();
      // Search for labels in find part
      PosInOccurrence pio = tacletApp.posInOccurrence();
      if (pio != null) {
         Term term = pio.subTerm();
         if (term != null) {
            // Check for evaluated truth values
            TermLabel label = term.getLabel(termLabelName);
            if (label instanceof PredicateTermLabel) {
               result.add(new PredicateLabelOccurrence((PredicateTermLabel) label, pio.isInAntec()));
            }
         }
      }
      // Search for labels in assumes part
      if (tacletApp.ifFormulaInstantiations() != null) {
         for (IfFormulaInstantiation inst : tacletApp.ifFormulaInstantiations()) {
            SequentFormula sf = inst.getConstrainedFormula();
            Term instTerm = sf.formula();
            TermLabel label = instTerm.getLabel(termLabelName);
            if (label instanceof PredicateTermLabel) {
               boolean inAntecedent = sequent.antecedent().contains(sf);
               result.add(new PredicateLabelOccurrence((PredicateTermLabel) label, inAntecedent));
            }
         }
      }
      return result;
   }
   
   private static class PredicateLabelOccurrence {
      private final PredicateTermLabel label;
      private final boolean inAntecedent;
      
      public PredicateLabelOccurrence(PredicateTermLabel label, boolean inAntecedent) {
         super();
         this.label = label;
         this.inAntecedent = inAntecedent;
      }

      public PredicateTermLabel getLabel() {
         return label;
      }

      public boolean isInAntecedent() {
         return inAntecedent;
      }

      @Override
      public String toString() {
         return label + (inAntecedent ? " in antecedent" : " in succedent");
      }
   }

   /**
    * Analyzes the given {@link TacletGoalTemplate}.
    * @param parent The current {@link Node} on which the rule was applied.
    * @param tacletApp The {@link TacletApp}.
    * @param tacletGoal The {@link TacletGoalTemplate}.
    * @param labels The {@link PredicateTermLabel}s.
    * @param servies The {@link Services} to use.
    * @param results The {@link Map} with all available {@link PredicateResult}s.
    */
   private static void analyzeTacletGoal(Node parent, 
                                         TacletApp tacletApp, 
                                         TacletGoalTemplate tacletGoal, 
                                         List<PredicateLabelOccurrence> labels, 
                                         Services services,
                                         Map<String, IPredicateInstruction> results) {
      Object replaceObject = tacletGoal.replaceWithExpressionAsObject();
      if (replaceObject instanceof Term) {
         Term replaceTerm = SymbolicExecutionUtil.instantiateTerm(parent, (Term) replaceObject, tacletApp, services);
         for (PredicateLabelOccurrence Occurrence : labels) {
            // Check for true/false terms
            if (replaceTerm.op() == Junctor.TRUE) {
               updatePredicateResult(Occurrence.getLabel(), new PredicateResult(PredicateValue.TRUE, parent), results);
            }
            else if (replaceTerm.op() == Junctor.FALSE) {
               updatePredicateResult(Occurrence.getLabel(), new PredicateResult(PredicateValue.FALSE, parent), results);
            }
         }
      }
   }
   
   protected static void updatePredicateResultBasedOnNewMinorIds(final Node childNode,
                                                                 final Name termLabelName,
                                                                 final TermBuilder tb,
                                                                 final Map<String, IPredicateInstruction> results) {
      Node parentNode = childNode.parent();
      final PosInOccurrence pio = parentNode.getAppliedRuleApp().posInOccurrence();
      if (pio != null) {
         // Check application term and all of its children and grand children
         pio.subTerm().execPreOrder(new DefaultVisitor() {
            @Override
            public void visit(Term visited) {
               checkForNewMinorIds(childNode, visited, termLabelName, pio, tb, results);
            }
         });
         // Check application term parents
         PosInOccurrence currentPio = pio;
         while (!currentPio.isTopLevel()) {
            currentPio = currentPio.up();
            checkForNewMinorIds(childNode, currentPio.subTerm(), termLabelName, pio, tb, results);
         }
      }
   }
   
   protected static void checkForNewMinorIds(Node childNode, 
                                             Term term, 
                                             Name termLabelName, 
                                             PosInOccurrence pio, 
                                             TermBuilder tb, 
                                             Map<String, IPredicateInstruction> results) {
      TermLabel label = term.getLabel(termLabelName);
      if (label instanceof PredicateTermLabel) {
         Term replacement = checkForNewMinorIds(childNode, (PredicateTermLabel) label, pio.isInAntec(), tb);
         if (replacement != null) {
            updatePredicateResult((PredicateTermLabel) label, new TermPredicateInstruction(replacement), results);
         }
      }
   }

   protected static Term checkForNewMinorIds(Node childNode, 
                                             PredicateTermLabel label,
                                             boolean antecedentRuleApplication,
                                             TermBuilder tb) {
      // Search replacements
      List<Term> antecedentReplacements = new LinkedList<Term>();
      List<Term> succedentReplacements = new LinkedList<Term>();
      for (SequentFormula sf : childNode.sequent().antecedent()) {
         findLabelReplacements(sf, label.name(), label.getId(), antecedentReplacements);
      }
      for (SequentFormula sf : childNode.sequent().succedent()) {
         findLabelReplacements(sf, label.name(), label.getId(), succedentReplacements);
      }
      // Compute term
      return createSequentTerm(antecedentReplacements, succedentReplacements, antecedentRuleApplication, tb);
   }
   
   protected static Term createSequentTerm(List<Term> antecedentReplacements, 
                                           List<Term> succedentReplacements, 
                                           boolean antecedentRuleApplication, 
                                           TermBuilder tb) {
      if (!antecedentReplacements.isEmpty() && !succedentReplacements.isEmpty()) {
         Term left = tb.andMaintainLabels(antecedentReplacements);
         Term right = tb.orMaintainLabels(succedentReplacements);
         if (antecedentRuleApplication) {
            throw new UnsupportedOperationException();
         }
         else {
            return tb.impMaintainLabels(left, right);
         }
      }
      else if (!antecedentReplacements.isEmpty()) {
         Term left = tb.andMaintainLabels(antecedentReplacements);
         if (antecedentRuleApplication) {
            return left;
         }
         else {
            return tb.notMaintainLabels(left);
         }
      }
      else if (!succedentReplacements.isEmpty()) {
         Term right = tb.orMaintainLabels(succedentReplacements);
         if (!antecedentRuleApplication) {
            return right;
         }
         else {
            return tb.notMaintainLabels(right);
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
               String[] beforeIds = pLabel.getBeforeIds();
               if (JavaUtil.contains(beforeIds, labelId)) {
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
       * Returns the leaf {@link Node}.
       * @return The leaf {@link Node}.
       */
      public Node getLeafNode() {
         return leafNode;
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
         return evaluateTerm(term, termLabelName, results);
      }
      
      public static PredicateResult evaluateTerm(Term term, Name termLabelName, Map<String, IPredicateInstruction> results) {
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
             term.op() == Junctor.OR ||
             term.op() == Equality.EQV) {
            Term leftTerm = TermBuilder.goBelowUpdates(term.sub(0));
            Term rightTerm = TermBuilder.goBelowUpdates(term.sub(1));
            TermLabel leftLabel = leftTerm.getLabel(termLabelName);
            TermLabel rightLabel = rightTerm.getLabel(termLabelName);
            IPredicateInstruction leftInstruction = leftLabel instanceof PredicateTermLabel ? results.get(((PredicateTermLabel) leftLabel).getId()) : null;
            IPredicateInstruction rightInstruction = rightLabel instanceof PredicateTermLabel ? results.get(((PredicateTermLabel) rightLabel).getId()) : null;
            PredicateResult leftResult = leftInstruction != null ? leftInstruction.evaluate(termLabelName, results) : evaluateTerm(leftTerm, termLabelName, results);
            PredicateResult rightResult = rightInstruction != null ? rightInstruction.evaluate(termLabelName, results) : evaluateTerm(rightTerm, termLabelName, results);
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
            else if (term.op() == Equality.EQV) {
               resultValue = PredicateValue.eqv(leftValue, rightValue);
            }
            else {
               throw new IllegalStateException("Operator '" + term.op() + "' is not supported.");
            }
            return new PredicateResult(resultValue, 
                                       leftResult != null ? leftResult.getNodes() : null,
                                       rightResult != null ? rightResult.getNodes() : null);
         }
         else if (term.op() == Junctor.NOT) {
            Term argumentTerm = TermBuilder.goBelowUpdates(term.sub(0));
            TermLabel argumentLabel = argumentTerm.getLabel(termLabelName);
            IPredicateInstruction argumentInstruction = argumentLabel instanceof PredicateTermLabel ? results.get(((PredicateTermLabel) argumentLabel).getId()) : null;
            PredicateResult argumentResult = argumentInstruction != null ? argumentInstruction.evaluate(termLabelName, results) : evaluateTerm(argumentTerm, termLabelName, results);
            PredicateValue argumentValue = argumentResult != null ? argumentResult.getValue() : null;
            PredicateValue resultValue = PredicateValue.not(argumentValue);
            return new PredicateResult(resultValue, 
                                       argumentResult != null ? argumentResult.getNodes() : null);
         }
         else if (isIfThenElseFormula(term)) {
            Term conditionTerm = TermBuilder.goBelowUpdates(term.sub(0));
            Term thenTerm = TermBuilder.goBelowUpdates(term.sub(1));
            Term elseTerm = TermBuilder.goBelowUpdates(term.sub(2));
            TermLabel conditionLabel = conditionTerm.getLabel(termLabelName);
            TermLabel thenLabel = thenTerm.getLabel(termLabelName);
            TermLabel elseLabel = elseTerm.getLabel(termLabelName);
            IPredicateInstruction conditionInstruction = conditionLabel instanceof PredicateTermLabel ? results.get(((PredicateTermLabel) conditionLabel).getId()) : null;
            IPredicateInstruction thenInstruction = thenLabel instanceof PredicateTermLabel ? results.get(((PredicateTermLabel) thenLabel).getId()) : null;
            IPredicateInstruction elseInstruction = elseLabel instanceof PredicateTermLabel ? results.get(((PredicateTermLabel) elseLabel).getId()) : null;
            PredicateResult conditionResult = conditionInstruction != null ? conditionInstruction.evaluate(termLabelName, results) : evaluateTerm(conditionTerm, termLabelName, results);
            PredicateResult thenResult = thenInstruction != null ? thenInstruction.evaluate(termLabelName, results) : evaluateTerm(thenTerm, termLabelName, results);
            PredicateResult elseResult = elseInstruction != null ? elseInstruction.evaluate(termLabelName, results) : evaluateTerm(elseTerm, termLabelName, results);
            PredicateValue conditionValue = conditionResult != null ? conditionResult.getValue() : null;
            PredicateValue thenValue = thenResult != null ? thenResult.getValue() : null;
            PredicateValue elseValue = elseResult != null ? elseResult.getValue() : null;
            PredicateValue resultValue = PredicateValue.ifThenElse(conditionValue, thenValue, elseValue);
            return new PredicateResult(resultValue, 
                                       conditionResult != null ? conditionResult.getNodes() : null,
                                       thenResult != null ? thenResult.getNodes() : null,
                                       elseResult != null ? elseResult.getNodes() : null);
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

      /**
       * Computes the {@code eqv} value.
       * @param value The {@link PredicateValue}.
       * @return The computed {@code not} value.
       */
      public static PredicateValue eqv(PredicateValue left, PredicateValue right) {
         return or(and(left, right), and(not(left), not(right)));
      }

      /**
       * Computes the {@code if-then-else} value.
       * @param conditionValue The condition value.
       * @param thenValue The then value.
       * @param elseValue The else value.
       * @return The computed {@code if-then-else} value.
       */
      public static PredicateValue ifThenElse(PredicateValue conditionValue,
                                              PredicateValue thenValue, 
                                              PredicateValue elseValue) {
         if (TRUE.equals(conditionValue)) {
            return thenValue;
         }
         else if (FALSE.equals(conditionValue)) {
            return elseValue;
         }
         else {
            return UNKNOWN;
         }
      }
   }
}
