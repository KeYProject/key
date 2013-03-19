package de.uka.ilkd.key.rule;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

public class LabelInstantiatorDispatcher {
   private PosInOccurrence applicationPosInOccurrence;
   
   private Rule rule;

   private ImmutableList<ILabelInstantiator> labelInstantiators;
   
   public LabelInstantiatorDispatcher(PosInOccurrence applicationPosInOccurrence, Rule rule, ImmutableList<ILabelInstantiator> labelInstantiators) {
      this.applicationPosInOccurrence = applicationPosInOccurrence;
      this.rule = rule;
      this.labelInstantiators = labelInstantiators;
   }
   
   public ImmutableArray<ITermLabel> instantiateLabels(Term tacletTerm, 
                                                       Operator newTermOp, 
                                                       ImmutableArray<Term> newTermSubs, 
                                                       ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                       JavaBlock newTermJavaBlock) {
      return instantiateLabels(labelInstantiators, applicationPosInOccurrence, rule, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock);
   }

   public static Term label(Services services,
                            Rule rule,
                            PosInOccurrence applicationPosInOccurrence, 
                            Term term) {
      return TermBuilder.DF.label(term, instantiateLabels(services, applicationPosInOccurrence, rule, null, term.op(), term.subs(), term.boundVars(), term.javaBlock()));
   }
   
   public static ImmutableArray<ITermLabel> instantiateLabels(Services services,
         PosInOccurrence applicationPosInOccurrence,
         Rule rule,
         Term tacletTerm, 
         Operator newTermOp, 
         ImmutableArray<Term> newTermSubs, 
         ImmutableArray<QuantifiableVariable> newTermBoundVars,
         JavaBlock newTermJavaBlock) {
      return instantiateLabels(services.getProof().getSettings().getLabelInstantiators(), applicationPosInOccurrence, rule, tacletTerm, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock);
   }
   
   public static ImmutableArray<ITermLabel> instantiateLabels(ImmutableList<ILabelInstantiator> labelInstantiators,
                                                              PosInOccurrence applicationPosInOccurrence,
                                                              Rule rule,
                                                              Term tacletTerm, 
                                                              Operator newTermOp, 
                                                              ImmutableArray<Term> newTermSubs, 
                                                              ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                                              JavaBlock newTermJavaBlock) {
      List<ITermLabel> instantiatedLabels = new LinkedList<ITermLabel>();
      if (labelInstantiators != null) {
         for (ILabelInstantiator instantiator : labelInstantiators) {
            instantiatedLabels.addAll(instantiator.instantiateLabels(tacletTerm, applicationPosInOccurrence, applicationPosInOccurrence != null ? applicationPosInOccurrence.subTerm() : null, rule, newTermOp, newTermSubs, newTermBoundVars, newTermJavaBlock));
         }
      }
      return new ImmutableArray<ITermLabel>(instantiatedLabels);
   }
}