package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Provides a basic implementation of {@link IExecutionValue}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionValue extends AbstractExecutionElement implements IExecutionValue {
   /**
    * The parent {@link IExecutionVariable} which provides this {@link IExecutionValue}.
    */
   private final IExecutionVariable variable;

   /**
    * The condition under which the variable has this value.
    */
   private final Term condition;
   
   /**
    * The {@link IExecutionConstraint}s.
    */
   private IExecutionConstraint[] constraints;
   
   /**
    * The value.
    */
   private final Term value;
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param variable The parent {@link IExecutionVariable} which contains this value.
    * @param condition The condition.
    * @param value The value.
    */
   public AbstractExecutionValue(ITreeSettings settings, 
                                 KeYMediator mediator, 
                                 Node proofNode, 
                                 IExecutionVariable variable, 
                                 Term condition,
                                 Term value) {
      super(settings, mediator, proofNode);
      this.variable = variable;
      this.condition = condition;
      this.value = value;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionConstraint[] getConstraints() throws ProofInputException {
      synchronized (this) {
         if (constraints == null) {
            constraints = lazyComputeConstraints();
         }
         return constraints;
      }
   }
   
   /**
    * Computes the related constraints lazily when {@link #getConstraints()} is called the first time.
    * @return The related {@link IExecutionConstraint}s.
    * @throws ProofInputException Occurred Exception
    */
   protected IExecutionConstraint[] lazyComputeConstraints() throws ProofInputException {
      if (!isDisposed() && !isValueUnknown()) {
         List<IExecutionConstraint> constraints = new LinkedList<IExecutionConstraint>();
         IExecutionConstraint[] allConstraints = getNodeConstraints();
         Set<Term> relevantTerms = collectRelevantTerms(getServices(), getValue());
         for (IExecutionConstraint constraint : allConstraints) {
            if (containsTerm(constraint.getTerm(), relevantTerms)) {
               constraints.add(constraint);
            }
         }
         return constraints.toArray(new IExecutionConstraint[constraints.size()]);
      }
      else {
         return new IExecutionConstraint[0];
      }
   }
   
   /**
    * Returns all available {@link IExecutionConstraint}s of the {@link IExecutionNode} on which this {@link IExecutionValue} is part of.
    * @return All available {@link IExecutionConstraint}s.
    */
   protected abstract IExecutionConstraint[] getNodeConstraints();
   
   /**
    * Collects all {@link Term}s contained in relevant constraints.
    * @param services The {@link Services} to use.
    * @param term The initial {@link Term}.
    * @return The relevant {@link Term}s.
    */
   protected Set<Term> collectRelevantTerms(Services services, Term term) {
      final Set<Term> terms = new HashSet<Term>();
      fillRelevantTerms(services, term, terms);
      return terms;
   }
   
   /**
    * Utility method used by {@link #collectRelevantTerms(Services, Term)}.
    * @param services The {@link Services} to use.
    * @param term The initial {@link Term}.
    * @param toFill The {@link Set} of relevant {@link Term}s to fill.
    */
   protected void fillRelevantTerms(Services services, Term term, Set<Term> toFill) {
      if (term != null) {
         if (term.op() instanceof ProgramVariable ||
             SymbolicExecutionUtil.isSelect(services, term)) {
            toFill.add(term);
         }
         else {
            for (int i = 0; i < term.arity(); i++) {
               fillRelevantTerms(services, term.sub(i), toFill);
            }
         }
      }
   }

   /**
    * Checks if the given {@link Term} contains at least one of the given once.
    * @param term The {@link Term} to search in.
    * @param toSearch The {@link Term}s to search.
    * @return {@code true} at least one {@link Term} is contained, {@code false} none of the {@link Term}s is contained.
    */
   protected boolean containsTerm(Term term, Set<Term> toSearch) {
      if (toSearch.contains(term)) {
         return true;
      }
      else {
         boolean contained = false;
         int i = 0;
         while (!contained && i < term.arity()) {
            contained = containsTerm(term.sub(i), toSearch);
            i++;
         }
         return contained;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionVariable getVariable() {
      return variable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PosInOccurrence getModalityPIO() {
      return getVariable().getModalityPIO();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      String conditionString = getConditionString();
      if (conditionString != null) {
         return getVariable().getName() + " {" + getConditionString() + "}";
      }
      else {
         return getVariable().getName();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Value";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getCondition() throws ProofInputException {
      return condition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getValue() throws ProofInputException {
      return value;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isValueAnObject() throws ProofInputException {
      if (isValueUnknown()) {
         return false;
      }
      else {
         Term value = getValue();
         return SymbolicExecutionUtil.hasReferenceSort(getServices(), value);
      }
   }
}
