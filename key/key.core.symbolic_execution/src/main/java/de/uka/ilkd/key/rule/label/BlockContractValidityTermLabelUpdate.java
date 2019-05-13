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

package de.uka.ilkd.key.rule.label;

import java.util.Set;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.BlockContractValidityTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.BlockContractInternalRule;
import de.uka.ilkd.key.rule.LoopContractInternalRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Makes sure that {@link BlockContractValidityTermLabel} is introduced
 * when a {@link BlockContractInternalRule} is applied.
 * @author Martin Hentschel
 */
public class BlockContractValidityTermLabelUpdate implements TermLabelUpdate {
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<Name> getSupportedRuleNames() {
      return ImmutableSLList.<Name>nil().append(BlockContractInternalRule.INSTANCE.name());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateLabels(TermLabelState state,
                            Services services,
                            PosInOccurrence applicationPosInOccurrence,
                            Term applicationTerm,
                            Term modalityTerm,
                            Rule rule,
                            RuleApp ruleApp,
                            Object hint,
                            Term tacletTerm,
                            Operator newTermOp,
                            ImmutableArray<Term> newTermSubs,
                            ImmutableArray<QuantifiableVariable> newTermBoundVars,
                            JavaBlock newTermJavaBlock,
                            Set<TermLabel> labels) {
       if ((rule instanceof BlockContractInternalRule
    		   || rule instanceof LoopContractInternalRule)
    		   && ((BlockContractInternalRule.BlockContractHint)hint).getExceptionalVariable()
    		   		!= null 
               && SymbolicExecutionUtil.hasSymbolicExecutionLabel(modalityTerm)) {
           if (CollectionUtil.search(labels, new IFilter<TermLabel>() {
               @Override
               public boolean select(TermLabel element) {
                   return element instanceof BlockContractValidityTermLabel;
               }
           }) == null) {
               labels.add(new BlockContractValidityTermLabel(((BlockContractInternalRule.BlockContractHint)hint).getExceptionalVariable()));
           }
      }
   }
}