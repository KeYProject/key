package de.uka.ilkd.key.rule.label;

import java.util.HashSet;
import java.util.Set;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Rule;

public class OriginTermLabelPolicy implements TermLabelPolicy {

    @Override
    public TermLabel keepLabel(TermLabelState state, Services services,
            PosInOccurrence applicationPosInOccurrence, Term applicationTerm, Rule rule, Goal goal,
            Object hint, Term tacletTerm, Operator newTermOp, ImmutableArray<Term> newTermSubs,
            ImmutableArray<QuantifiableVariable> newTermBoundVars, JavaBlock newTermJavaBlock,
            ImmutableArray<TermLabel> newTermOriginalLabels, TermLabel label) {
        //System.out.println("newTermOriginalLabels " + newTermOriginalLabels);
        //System.out.println("label                 " + label);

        OriginTermLabel newLabel = (OriginTermLabel) label;
        OriginTermLabel oldLabel = null;
        
        for (TermLabel l : newTermOriginalLabels) {
            if (l instanceof OriginTermLabel && l != newLabel) {
                oldLabel = (OriginTermLabel) l;
            }
        }
        
        if (oldLabel == null) {
            return newLabel;
        } else {
            Set<Origin> origins = new HashSet<>();
            origins.add(newLabel.getOrigin());
            origins.addAll(newLabel.getSubtermOrigins());
            return new OriginTermLabel(
                    oldLabel.getOrigin().specType,
                    oldLabel.getOrigin().fileName,
                    oldLabel.getOrigin().line,
                    origins);
        }
    }
}

