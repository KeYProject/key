/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.po;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.POExtension;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;

import org.key_project.util.collection.ImmutableArray;

/**
 * Implementation of {@link POExtension} to support truth value evaluation.
 *
 * @author Martin Hentschel
 */
public class TruthValuePOExtension implements POExtension {
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isPOSupported(ProofOblInput po) {
        return po instanceof AbstractOperationPO;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm modifyPostTerm(AbstractOperationPO abstractOperationPO, InitConfig proofConfig,
            Services services, ProgramVariable selfTerm,
            JTerm postTerm) {
        if (SymbolicExecutionJavaProfile.isTruthValueEvaluationEnabled(proofConfig)) {
            return labelPostTerm(services, postTerm);
        } else {
            return postTerm;
        }
    }

    /**
     * Labels all predicates in the given {@link JTerm} and its children with a
     * {@link FormulaTermLabel}.
     *
     * @param services The {@link Services} to use.
     * @param term The {@link JTerm} to label.
     * @return The labeled {@link JTerm}.
     */
    protected JTerm labelPostTerm(Services services, JTerm term) {
        if (term != null) {
            final TermFactory tf = services.getTermFactory();
            // Label children of operator
            if (TruthValueTracingUtil.isLogicOperator(term)) {
                JTerm[] newSubs = new JTerm[term.arity()];
                boolean subsChanged = false;
                for (int i = 0; i < newSubs.length; i++) {
                    JTerm oldTerm = term.sub(i);
                    newSubs[i] = labelPostTerm(services, oldTerm);
                    if (oldTerm != newSubs[i]) {
                        subsChanged = true;
                    }
                }
                term = subsChanged
                        ? tf.createTerm(term.op(), new ImmutableArray<>(newSubs),
                            term.boundVars(), term.getLabels())
                        : term;
            }
            ImmutableArray<TermLabel> oldLabels = term.getLabels();
            TermLabel[] newLabels = oldLabels.toArray(new TermLabel[oldLabels.size() + 1]);
            int labelID =
                services.getCounter(FormulaTermLabel.PROOF_COUNTER_NAME).getCountPlusPlus();
            int labelSubID = FormulaTermLabel.newLabelSubID(services, labelID);
            newLabels[oldLabels.size()] = new FormulaTermLabel(labelID, labelSubID);
            return tf.createTerm(term.op(), term.subs(), term.boundVars(),
                new ImmutableArray<>(newLabels));
        } else {
            return null;
        }
    }
}
