/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionSideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.prover.engine.impl.ApplyStrategyInfo;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;

import org.jspecify.annotations.NonNull;

/**
 * An implementation of {@link IExecutionVariable} used to query all array indices at the same time.
 * This supports also arrays where the length is symbolic and not a concrete number.
 *
 * @author Martin Hentschel
 */
public class ExecutionAllArrayIndicesVariable extends ExecutionVariable {
    /**
     * The name of the constant used to query the value of all array indices.
     */
    public static final String ARRAY_INDEX_CONSTANT_NAME = "*";

    /**
     * The name used to represent the fact that a value is not available.
     */
    public static final String NOT_A_VALUE_NAME = "<Not a Value>";

    /**
     * The constant representing an arbitrary array index.
     */
    private JTerm constant;

    /**
     * The constant representing the fact that no value is available.
     */
    private final JTerm notAValue;

    /**
     * Constructor.
     *
     * @param parentNode The parent {@link IExecutionNode}.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     * @param modalityPIO The {@link PosInOccurrence} of the modality of interest.
     * @param parentValue The parent {@link IExecutionValue} representing the array.
     * @param arrayProgramVariable The {@link IProgramVariable} of the array.
     * @param additionalCondition An optional additional condition to consider.
     */
    public ExecutionAllArrayIndicesVariable(IExecutionNode<?> parentNode, Node proofNode,
            PosInOccurrence modalityPIO, ExecutionValue parentValue,
            IProgramVariable arrayProgramVariable, JTerm additionalCondition) {
        super(parentNode, proofNode, modalityPIO, parentValue, arrayProgramVariable,
            additionalCondition);
        assert parentValue != null;
        TermBuilder tb = getServices().getTermBuilder();
        Function notAValueFunction =
            new JFunction(new Name(tb.newName(NOT_A_VALUE_NAME)), JavaDLTheory.ANY);
        notAValue = tb.func(notAValueFunction);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeName() throws ProofInputException {
        // Ensure that constant is defined
        if (constant == null) {
            getValues();
        }
        // Compute name
        String arrayName = super.lazyComputeName();
        return arrayName + "[" + constant + "]";
    }

    /**
     * Computes the value for {@link #getValues()} lazily when the method is called the first time.
     *
     * @throws ProofInputException Occurred Exception.
     */
    protected ExecutionValue[] lazyComputeValues() throws ProofInputException {
        InitConfig initConfig = getInitConfig();
        if (initConfig != null) { // Otherwise proof is disposed.
            // New OneStepSimplifier is required because it has an internal state and the default
            // instance can't be used parallel.
            final ProofEnvironment sideProofEnv = SymbolicExecutionSideProofUtil
                    .cloneProofEnvironmentWithOwnOneStepSimplifier(initConfig, true);
            final Services sideServices = sideProofEnv.getServicesForEnvironment();
            final TermBuilder tb = sideServices.getTermBuilder();
            // Start site proof to extract the value of the result variable.
            JTerm siteProofCondition = getAdditionalCondition() != null
                    ? tb.and(getAdditionalCondition(), getParentValue().getCondition())
                    : getParentValue().getCondition();
            JTerm arrayTerm = createArrayTerm();
            // Create index constant
            Function constantFunction =
                new JFunction(new Name(tb.newName(ARRAY_INDEX_CONSTANT_NAME)),
                    sideServices.getTypeConverter().getIntegerLDT().targetSort());
            constant = tb.func(constantFunction);
            setName(lazyComputeName()); // Update name because constant has changed
            JTerm arrayIndex = tb.dotArr(arrayTerm, constant);
            // Create if check
            Function arrayLengthFunction =
                sideServices.getTypeConverter().getHeapLDT().getLength();
            JTerm arrayRange = tb.and(tb.geq(constant, tb.zero()),
                tb.lt(constant, tb.func(arrayLengthFunction, arrayTerm)));
            JTerm resultIf = tb.ife(arrayRange, arrayIndex, notAValue);

            // Create predicate which will be used in formulas to store the value interested in.
            Function resultPredicate =
                new JFunction(new Name(tb.newName("ResultPredicate")),
                    JavaDLTheory.FORMULA, resultIf.sort());
            // Create formula which contains the value interested in.
            JTerm resultTerm = tb.func(resultPredicate, resultIf);
            // Create Sequent to prove with new succedent.
            Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(
                getProofNode(), getModalityPIO(), siteProofCondition, resultTerm, false);
            // Perform side proof
            ApplyStrategyInfo<@NonNull Proof, Goal> info =
                SymbolicExecutionSideProofUtil.startSideProof(getProof(),
                    sideProofEnv, sequent, StrategyProperties.METHOD_NONE,
                    StrategyProperties.LOOP_NONE,
                    StrategyProperties.QUERY_OFF, StrategyProperties.SPLITTING_DELAYED);
            try {
                return instantiateValuesFromSideProof(initConfig, sideServices, tb, info,
                    resultPredicate, arrayTerm, // Pass array to ensure that unknown values are
                                                // correctly computed.
                    siteProofCondition);
            } finally {
                SymbolicExecutionSideProofUtil.disposeOrStore(
                    "All array indices value computation on node " + getProofNode().serialNr(),
                    info);
            }
        } else {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected boolean isValidValue(JTerm value) {
        return notAValue != value;
    }

    /**
     * Creates a {@link JTerm} to access the array.
     *
     * @return The {@link JTerm} to access the array.
     */
    public JTerm createArrayTerm() {
        return getParentValue().getVariable().createSelectTerm();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm createSelectTerm() {
        assert constant != null : "Call getValues() before calling createSelectTerm().";
        return getServices().getTermBuilder().dotArr(createArrayTerm(), constant);
    }

    /**
     * Returns the constant representing an arbitrary array index.
     *
     * @return The constant representing an arbitrary array index.
     */
    public JTerm getConstant() {
        return constant;
    }

    /**
     * Returns the constant representing the fact that no value is available.
     *
     * @return The constant representing the fact that no value is available.
     */
    public JTerm getNotAValue() {
        return notAValue;
    }
}
