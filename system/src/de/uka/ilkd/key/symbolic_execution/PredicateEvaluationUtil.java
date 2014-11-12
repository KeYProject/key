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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.TermTransformer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;

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
    * Evaluates the truth values in the subtree of the given {@link Node}
    * for predicates labeled with the given {@link TermLabel} name.
    * @param node The {@link Node} to start evaluation at.
    * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
    * @return The result.
    * @throws ProofInputException Occurred Exception
    */
   public static PredicateEvaluationResult evaluate(Node node, 
                                                    Name termLabelName) throws ProofInputException {
      PredicateEvaluationResult result = new PredicateEvaluationResult();
      Deque<Map<TermLabel, PredicateResult>> evaluationStack = new LinkedList<Map<TermLabel,PredicateResult>>();
      evaluationStack.addFirst(new HashMap<TermLabel, PredicateResult>());
      evaluateNode(node, termLabelName, evaluationStack, result);
      return result;
   }

   /**
    * Utility method used by {@link #evaluate(Node, Name)} for recursive evaluation.
    * @param node The current {@link Node}.
    * @param termLabelName The {@link Name} of the {@link TermLabel} to consider.
    * @param evaluationStack The not empty stack with evaluation results.
    * @param result The {@link PredicateEvaluationResult} to fill with leaf nodes.
    * @throws ProofInputException Occurred Exception
    */
   private static void evaluateNode(final Node node, 
                                    final Name termLabelName, 
                                    final Deque<Map<TermLabel, PredicateResult>> evaluationStack, 
                                    final PredicateEvaluationResult result) throws ProofInputException {
      // Create new stack entry
      final Map<TermLabel, PredicateResult> currentResults = evaluationStack.getFirst();
      // Analyze applied rule
      boolean childrenAlreadyTreated = false;
      if (node.getAppliedRuleApp() instanceof TacletApp) {
         TacletApp tacletApp = (TacletApp) node.getAppliedRuleApp();
         PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
         if (pio != null) {
            Term term = pio.subTerm();
            if (term != null) {
               TermLabel label = getPredicateLabel(term, termLabelName);
               if (label != null) {
                  Taclet taclet = ((TacletApp) tacletApp).taclet();
                  if (taclet.goalTemplates().size() >= 1) { // Not a closing taclet
                     childrenAlreadyTreated = true;
                     int i = 0;
                     for (TacletGoalTemplate tacletGoal : taclet.goalTemplates()) {
                        Map<TermLabel, PredicateResult> childResults = new HashMap<TermLabel, PredicateResult>(currentResults);
                        analyzeTacletGoal(node, tacletApp, tacletGoal, label, childResults);
                        // Evaluate children with branch specific Taclet result
                        evaluationStack.addFirst(childResults);
                        evaluateNode(node.child(i), termLabelName, evaluationStack, result);
                        evaluationStack.removeFirst();
                        i++;
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
               TermLabel label = getPredicateLabel(protocolApp.posInOccurrence().subTerm(), termLabelName);
               if (label != null) {
                  TacletApp tacletApp = (TacletApp) protocolApp;
                  Taclet taclet = tacletApp.taclet();
                  assert taclet.goalTemplates().size() == 1;
                  analyzeTacletGoal(node, tacletApp, taclet.goalTemplates().head(), label, currentResults);
               }
            }
         }
      }
      // Analyze children
      int childCount = node.childrenCount();
      if (childCount == 0) {
         result.addBranchResult(new BranchResult(node, currentResults));
      }
      else if (!childrenAlreadyTreated) {
         // Evaluate children in case that branch specific Taclet results are not available and thus not evaluated yet.
         for (int i = 0; i < childCount; i++) {
            evaluationStack.addFirst(new HashMap<TermLabel, PredicateResult>(currentResults));
            evaluateNode(node.child(i), termLabelName, evaluationStack, result);
            evaluationStack.removeFirst();
         }
      }
   }
   
   /**
    * Analyzes the given {@link TacletGoalTemplate}.
    * @param node The current {@link Node}.
    * @param tacletApp The {@link TacletApp}.
    * @param tacletGoal The {@link TacletGoalTemplate}.
    * @param label The {@link TermLabel}.
    * @param results The {@link Map} with all available {@link PredicateResult}s.
    */
   private static void analyzeTacletGoal(Node node, 
                                         TacletApp tacletApp, 
                                         TacletGoalTemplate tacletGoal, 
                                         TermLabel label, 
                                         Map<TermLabel, PredicateResult> results) {
      Object replaceObject = tacletGoal.replaceWithExpressionAsObject();
      if (replaceObject instanceof Term) {
         Term replaceTerm = (Term) replaceObject;
         // Replace meta constructs
         if (replaceTerm.op() instanceof TermTransformer) {
            Services services = node.proof().getServices();
            SyntacticalReplaceVisitor visitor = new SyntacticalReplaceVisitor(services, tacletApp.instantiations(), tacletApp.posInOccurrence(), tacletApp.taclet());
            replaceTerm.execPostOrder(visitor);
            replaceTerm = visitor.getTerm();
         }
         // Check for true/false terms
         if (replaceTerm.op() == Junctor.TRUE) {
            updatePredicateResult(label, new PredicateResult(PredicateValue.TRUE, node), results);
         }
         else if (replaceTerm.op() == Junctor.FALSE) {
            updatePredicateResult(label, new PredicateResult(PredicateValue.FALSE, node), results);
         }
      }

   }

   /**
    * Updates the {@link PredicateResult} of the given {@link TermLabel}.
    * @param label The {@link TermLabel} to update its {@link PredicateResult}.
    * @param result The new {@link PredicateResult}.
    * @param results The {@link Map} with all available {@link PredicateResult}s.
    */
   private static void updatePredicateResult(TermLabel label, PredicateResult result, Map<TermLabel, PredicateResult> results) {
      PredicateResult oldResult = results.get(label);
      if (oldResult != null) {
         if (!oldResult.getValue().equals(result.getValue())) {
            PredicateResult newResult = new PredicateResult(PredicateValue.UNKNOWN, oldResult.getNodes(), result.getNodes());
            results.put(label, newResult);
         }
      }
      else {
         results.put(label, result);
      }
   }
   
   /**
    * Returns the first {@link TermLabel} with the given {@link Name}.
    * @param term The {@link Term}.
    * @param termLabelName The {@link Name}.
    * @return The found {@link TermLabel} or {@code null} otherwise.
    */
   public static TermLabel getPredicateLabel(Term term, final Name termLabelName) {
      if (term.hasLabels()) {
         return JavaUtil.search(term.getLabels(), new IFilter<TermLabel>() {
            @Override
            public boolean select(TermLabel element) {
               return JavaUtil.equals(element.name(), termLabelName);
            }
         });
      }
      else {
         return null;
      }
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
      private final Map<TermLabel, PredicateResult> results;
      
      /**
       * The leaf {@link Node}.
       */
      private final Node leafNode;
      
      /**
       * Constructor. 
       * @param leafNode All predicate results.
       * @param results The leaf {@link Node}.
       */
      public BranchResult(Node leafNode, 
                          Map<TermLabel, PredicateResult> results) {
         assert leafNode != null;
         assert results != null;
         this.leafNode = leafNode;
         this.results = results;
      }

      /**
       * Returns all predicate results.
       * @return All predicate results.
       */
      public Map<TermLabel, PredicateResult> getResults() {
         return Collections.unmodifiableMap(results);
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
         for (Entry<TermLabel, PredicateResult> entry : results.entrySet()) {
            if (afterFirst) {
               sb.append("\n");
            }
            else {
               afterFirst = true;
            }
            sb.append(entry.getKey());
            sb.append(" = ");
            sb.append(entry.getValue());
         }
         return sb.toString();
      }
   }
   
   /**
    * Represents the truth value of a predicate.
    * <b>This class needs to be unmodifiable.</b>
    * @author Martin Hentschel
    */
   public static class PredicateResult {
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
   }
}
