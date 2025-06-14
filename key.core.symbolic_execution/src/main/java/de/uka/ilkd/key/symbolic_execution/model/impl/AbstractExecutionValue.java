/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.*;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.prover.sequent.PosInOccurrence;

/**
 * Provides a basic implementation of {@link IExecutionValue}.
 *
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionValue extends AbstractExecutionElement
        implements IExecutionValue {
    /**
     * The parent {@link IExecutionVariable} which provides this {@link IExecutionValue}.
     */
    private final IExecutionVariable variable;

    /**
     * The condition under which the variable has this value.
     */
    private final JTerm condition;

    /**
     * The {@link IExecutionConstraint}s.
     */
    private IExecutionConstraint[] constraints;

    /**
     * The value.
     */
    private final JTerm value;

    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     * @param variable The parent {@link IExecutionVariable} which contains this value.
     * @param condition The condition.
     * @param value The value.
     */
    protected AbstractExecutionValue(ITreeSettings settings, Node proofNode,
            IExecutionVariable variable, JTerm condition, JTerm value) {
        super(settings, proofNode);
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
     * Computes the related constraints lazily when {@link #getConstraints()} is called the first
     * time.
     *
     * @return The related {@link IExecutionConstraint}s.
     * @throws ProofInputException Occurred Exception
     */
    protected IExecutionConstraint[] lazyComputeConstraints() throws ProofInputException {
        if (!isDisposed() && !isValueUnknown()) {
            List<IExecutionConstraint> constraints = new LinkedList<>();
            IExecutionConstraint[] allConstraints = getNodeConstraints();
            Set<JTerm> relevantTerms = collectRelevantTerms(getServices(), getValue());
            for (IExecutionConstraint constraint : allConstraints) {
                if (containsTerm(constraint.getTerm(), relevantTerms)) {
                    constraints.add(constraint);
                }
            }
            return constraints.toArray(new IExecutionConstraint[0]);
        } else {
            return new IExecutionConstraint[0];
        }
    }

    /**
     * Returns all available {@link IExecutionConstraint}s of the {@link IExecutionNode} on which
     * this {@link IExecutionValue} is part of.
     *
     * @return All available {@link IExecutionConstraint}s.
     */
    protected abstract IExecutionConstraint[] getNodeConstraints();

    /**
     * Collects all {@link JTerm}s contained in relevant constraints.
     *
     * @param services The {@link Services} to use.
     * @param term The initial {@link JTerm}.
     * @return The relevant {@link JTerm}s.
     */
    protected Set<JTerm> collectRelevantTerms(Services services, JTerm term) {
        final Set<JTerm> terms = new HashSet<>();
        fillRelevantTerms(services, term, terms);
        return terms;
    }

    /**
     * Utility method used by {@link #collectRelevantTerms(Services, JTerm)}.
     *
     * @param services The {@link Services} to use.
     * @param term The initial {@link JTerm}.
     * @param toFill The {@link Set} of relevant {@link JTerm}s to fill.
     */
    protected void fillRelevantTerms(Services services, JTerm term, Set<JTerm> toFill) {
        if (term != null) {
            if (term.op() instanceof ProgramVariable
                    || SymbolicExecutionUtil.isSelect(services, term)) {
                toFill.add(OriginTermLabel.removeOriginLabels(term, services));
            } else {
                for (int i = 0; i < term.arity(); i++) {
                    fillRelevantTerms(services, term.sub(i), toFill);
                }
            }
        }
    }

    /**
     * Checks if the given {@link JTerm} contains at least one of the given once.
     *
     * @param term The {@link JTerm} to search in.
     * @param toSearch The {@link JTerm}s to search.
     * @return {@code true} at least one {@link JTerm} is contained, {@code false} none of the
     *         {@link JTerm}s is contained.
     */
    protected boolean containsTerm(JTerm term, Set<JTerm> toSearch) {
        if (toSearch.contains(OriginTermLabel.removeOriginLabels(term, getServices()))) {
            return true;
        } else {
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
        } else {
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
    public JTerm getCondition() throws ProofInputException {
        return condition;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm getValue() throws ProofInputException {
        return value;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isValueAnObject() throws ProofInputException {
        if (isValueUnknown()) {
            return false;
        } else {
            JTerm value = getValue();
            return SymbolicExecutionUtil.hasReferenceSort(getServices(), value);
        }
    }
}
