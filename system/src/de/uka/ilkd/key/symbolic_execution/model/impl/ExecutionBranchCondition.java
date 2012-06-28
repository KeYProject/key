package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionBranchCondition}.
 * @author Martin Hentschel
 */
public class ExecutionBranchCondition extends AbstractExecutionNode implements IExecutionBranchCondition {
   /**
    * The {@link Term} which represents the branch condition.
    */
   private Term branchCondition;
   
   /**
    * The human readable branch condition.
    */
   private String formatedBranchCondition;
   
   /**
    * The path condition to reach this node.
    */
   private Term pathCondition;
   
   /**
    * The human readable path condition to reach this term.
    */
   private String formatedPathCondition;
   
   /**
    * Constructor.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionBranchCondition(KeYMediator mediator, Node proofNode) {
      super(mediator, proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return getProofNodeInfo().getBranchLabel();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Branch Condition";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedBranchCondition() throws ProofInputException {
      synchronized (this) {
         if (branchCondition == null) {
            lazyComputeBranchCondition();
         }
         return formatedBranchCondition;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getBranchCondition() throws ProofInputException {
      synchronized (this) {
         if (branchCondition == null) {
            lazyComputeBranchCondition();
         }
         return branchCondition;
      }
   }

   /**
    * Computes the branch condition lazily when {@link #getBranchCondition()}
    * or {@link #getFormatedBranchCondition()} is called the first time.
    * @throws ProofInputException Occurred Exception
    */
   protected void lazyComputeBranchCondition() throws ProofInputException {
      // Get applied taclet on parent proof node
      Node parent = getProofNode().parent();
      assert parent.getAppliedRuleApp() instanceof TacletApp; // Splits of built in rules are currently not supported.
      TacletApp app = (TacletApp)parent.getAppliedRuleApp();
      // Find goal template which has created the represented proof node
      int childIndex = JavaUtil.indexOf(parent.childrenIterator(), getProofNode());
      TacletGoalTemplate goalTemplate = app.taclet().goalTemplates().take(childIndex).head();
      // Apply instantiations of schema variables to sequent of goal template
      SVInstantiations instantiations = app.instantiations();
      ImmutableList<Term> antecedents = listSemisequentTerms(getServices(), instantiations, goalTemplate.sequent().antecedent());
      ImmutableList<Term> succedents = listSemisequentTerms(getServices(), instantiations, goalTemplate.sequent().succedent());
      // Construct branch condition from created antecedent and succedent terms as new implication 
      Term left = TermBuilder.DF.and(antecedents);
      Term right = TermBuilder.DF.or(succedents);
      Term implication = TermBuilder.DF.imp(left, right);
      // Check if an update context is available
      if (!instantiations.getUpdateContext().isEmpty()) {
         // Append update context because otherwise the formula is evaluated in wrong state
         branchCondition = TermBuilder.DF.applySequential(instantiations.getUpdateContext(), implication);
         // Simplify branch condition
         branchCondition = SymbolicExecutionUtil.simplify(getProof(), branchCondition);
      }
      else {
         // No update context, just use the implication as branch condition
         branchCondition = implication;
      }
      // Format branch condition
      StringBuffer sb = ProofSaver.printTerm(branchCondition, getServices(), true);
      formatedBranchCondition = sb.toString();
   }

   /**
    * Applies the schema variable instantiations on the given {@link Semisequent}.
    * @param services The {@link Services} to use.
    * @param svInst The schema variable instantiations.
    * @param semisequent The {@link Semisequent} to apply instantiations on.
    * @return The list of created {@link Term}s in which schema variables are replaced with the instantiation.
    */
   protected ImmutableList<Term> listSemisequentTerms(Services services, 
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
    * {@inheritDoc}
    */
   @Override
   public boolean isPathConditionChanged() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getPathCondition() throws ProofInputException {
      synchronized (this) {
         if (pathCondition == null) {
            lazyComputePathCondition();
         }
         return pathCondition;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedPathCondition() throws ProofInputException {
      synchronized (this) {
         if (pathCondition == null) {
            lazyComputePathCondition();
         }
         return formatedPathCondition;
      }
   }

   /**
    * Computes the path condition lazily when {@link #getPathCondition()}
    * or {@link #getFormatedPathCondition()} is called the first time.
    * @throws ProofInputException Occurred Exception
    */
   protected void lazyComputePathCondition() throws ProofInputException {
      // Get path to parent
      Term parentPath;
      if (getParent() != null) {
         parentPath = getParent().getPathCondition();
      }
      else {
         parentPath = TermBuilder.DF.tt();
      }
      // Add current branch condition to path
      pathCondition = TermBuilder.DF.and(parentPath, getBranchCondition());
      // Simplify path condition
      pathCondition = SymbolicExecutionUtil.simplify(getProof(), pathCondition);
      // Format path condition
      StringBuffer sb = ProofSaver.printTerm(pathCondition, getServices(), true);
      formatedPathCondition = sb.toString();
   }
}
