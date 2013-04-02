package de.uka.ilkd.key.rule;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.LoopBodyTermLabel;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Proof;

/**
 * <p>
 * This class provides static methods to manage {@link ITermLabelInstantiator}s.
 * </p>
 * <p>
 * In case of taclet rules, an instance of this class is used to collect the
 * additional information which is required to compute the new term labels
 * in the {@link SyntacticalReplaceVisitor}.
 * </p>
 * @author Martin Hentschel
 * @see ITermLabelInstantiator
 * @see ITermLabel
 */
public class TermLabelInstantiatorDispatcher {
   /**
    * The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten.
    */
   private PosInOccurrence applicationPosInOccurrence;
   
   /**
    * The {@link Rule} which is applied. 
    */
   private Rule rule;

   /**
    * The available {@link ITermLabelInstantiator}.
    */
   private ImmutableList<ITermLabelInstantiator> labelInstantiators;
   
   /**
    * Constructor.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param rule The {@link Rule} which is applied. 
    * @param labelInstantiators The available {@link ITermLabelInstantiator}.
    */
   public TermLabelInstantiatorDispatcher(PosInOccurrence applicationPosInOccurrence, 
                                          Rule rule, 
                                          ImmutableList<ITermLabelInstantiator> labelInstantiators) {
      this.applicationPosInOccurrence = applicationPosInOccurrence;
      this.rule = rule;
      this.labelInstantiators = labelInstantiators;
   }
   
   /**
    * Computes the {@link ITermLabel} to add to a new {@link Term} with
    * help of the {@link ITermLabelInstantiator}s available via {@link #labelInstantiators}.
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return The {@link ITermLabel}s to add to the new {@link Term} which should be created.
    * @return The {@link ITermLabel}s to add to the new {@link Term} which should be created.
    */
   public ImmutableArray<ITermLabel> instantiateLabels(Term tacletTerm, 
                                                       Operator newTermOp, 
                                                       ImmutableArray<Term> newTermSubs, 
                                                       ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                       JavaBlock newTermJavaBlock) {
      return instantiateLabels(labelInstantiators, applicationPosInOccurrence, rule, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock);
   }
   
   /**
    * Computes the {@link ITermLabel} to add to a new {@link Term} with
    * help of the {@link ITermLabelInstantiator}s provided by {@link Proof} of the given {@link Services}.
    * @param services The {@link Services} which contains the {@link Proof} that provides the {@link ITermLabelInstantiator}s to use.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param rule The {@link Rule} which is applied. 
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return The {@link ITermLabel}s to add to the new {@link Term} which should be created.
    */
   public static ImmutableArray<ITermLabel> instantiateLabels(Services services,
                                                              PosInOccurrence applicationPosInOccurrence,
                                                              Rule rule,
                                                              Term tacletTerm, 
                                                              Operator newTermOp, 
                                                              ImmutableArray<Term> newTermSubs, 
                                                              ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                              JavaBlock newTermJavaBlock) {
      return instantiateLabels(getLabelInstantiators(services), applicationPosInOccurrence, rule, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock);
   }
   
   /**
    * Returns all {@link ITermLabelInstantiator} contained in the {@link Proof} of the given {@link Services}.
    * @param services The {@link Services} which contains the proof to read {@link ITermLabelInstantiator}s from.
    * @return The {@link ITermLabelInstantiator}s contained in the {@link Proof} of the given {@link Services}.
    */
   public static ImmutableList<ITermLabelInstantiator> getLabelInstantiators(Services services) {
      return services.getProof().getSettings().getLabelSettings().getLabelInstantiators();
   }
   
   /**
    * Computes the {@link ITermLabel} to add to a new {@link Term} with
    * help of the given {@link ITermLabelInstantiator}s.
    * @param labelInstantiators The available {@link ITermLabelInstantiator}.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param rule The {@link Rule} which is applied. 
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return The {@link ITermLabel}s to add to the new {@link Term} which should be created.
    */
   public static ImmutableArray<ITermLabel> instantiateLabels(ImmutableList<ITermLabelInstantiator> labelInstantiators,
                                                              PosInOccurrence applicationPosInOccurrence,
                                                              Rule rule,
                                                              Term tacletTerm, 
                                                              Operator newTermOp, 
                                                              ImmutableArray<Term> newTermSubs, 
                                                              ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                              JavaBlock newTermJavaBlock) {
      List<ITermLabel> instantiatedLabels = new LinkedList<ITermLabel>();
      if (labelInstantiators != null) {
         for (ITermLabelInstantiator instantiator : labelInstantiators) {
            instantiatedLabels.addAll(instantiator.instantiateLabels(tacletTerm, applicationPosInOccurrence, applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null, rule, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock));
         }
      }
      return new ImmutableArray<ITermLabel>(instantiatedLabels);
   }

   /**
    * <p>
    * Returns the {@link ITermLabelInstantiator} with the given name if available.
    * </p>
    * <p>
    * This method has to be extended to support new {@link ITermLabelInstantiator}s.
    * </p>
    * @param name The name of the requested {@link ITermLabelInstantiator}.
    * @return The {@link ITermLabelInstantiator} or {@code null} if not available.
    */
   public static ITermLabelInstantiator getInstantiator(String name) {
      if (SymbolicExecutionTermLabel.NAME.toString().equals(name)) {
         return SymbolicExecutionTermLabelInstantiator.INSTANCE;
      }
      else if (LoopBodyTermLabel.NAME.toString().equals(name)) {
         return LoopBodyTermLabelInstantiator.INSTANCE;
      }
      else {
         return null;
      }
   }

   /**
    * Checks if the given {@link ITermLabelInstantiator} is used in the {@link Proof} of the given {@link Services}.
    * @param services The {@link Services} which provides the {@link Proof}.
    * @param instantiator The {@link ITermLabelInstantiator} to look for.
    * @return {@code true} {@link ITermLabelInstantiator} is available, {@code false} {@link ITermLabelInstantiator} is not available.
    */
   public static boolean hasInstantiator(Services services, ITermLabelInstantiator instantiator) {
      return getLabelInstantiators(services).contains(instantiator);
   }
}