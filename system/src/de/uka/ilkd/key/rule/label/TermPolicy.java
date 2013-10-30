package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;

public interface TermPolicy {
   /**
    * 
    * @param tacletTerm The {@link Term} in the taclet which is responsible to instantiate the new {@link Term} or {@code null} in case of build in rules. 
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten. 
    * @param applicationTerm The {@link Term} in the previous {@link Sequent} defined by the {@link PosInOccurrence} which is rewritten.
    * @param bestMatchTerm
    * @param rule The {@link Rule} which is applied. 
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param newTermOp The new {@link Operator} of the {@link Term} to create.
    * @param newTermSubs The optional children of the {@link Term} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link Term} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link Term} to create.
    * @return
    */
   public boolean keepLabel(Term tacletTerm, 
                            PosInOccurrence applicationPosInOccurrence,
                            Term applicationTerm,
                            Term bestMatchTerm,
                            Rule rule,
                            Goal goal,
                            Operator newTermOp, 
                            ImmutableArray<Term> newTermSubs, 
                            ImmutableArray<QuantifiableVariable> newTermBoundVars,
                            JavaBlock newTermJavaBlock);
}
