/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturnValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionSideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil.SiteProofVariableValueInput;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.prover.engine.impl.ApplyStrategyInfo;
import org.key_project.util.java.StringUtil;

/**
 * The default implementation of {@link IExecutionMethodReturn}.
 *
 * @author Martin Hentschel
 */
public class ExecutionMethodReturn extends AbstractExecutionMethodReturn<SourceElement>
        implements IExecutionMethodReturn {
    /**
     * The node name with signature including the return value.
     */
    private String signatureIncludingReturnValue;

    /**
     * The node name including the return value.
     */
    private String nameIncludingReturnValue;

    /**
     * The possible return values.
     */
    private IExecutionMethodReturnValue[] returnValues;

    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     * @param methodCall The {@link IExecutionMethodCall} which is now returned.
     */
    public ExecutionMethodReturn(ITreeSettings settings, Node proofNode,
            ExecutionMethodCall methodCall) {
        super(settings, proofNode, methodCall);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeName() throws ProofInputException {
        return createMethodReturnName(null, computeCalledMethodName());
    }

    /**
     * Computes the name of the called method.
     *
     * @return The name of the called method.
     */
    protected String computeCalledMethodName() {
        MethodReference explicitConstructorMR =
            getMethodCall().getExplicitConstructorMethodReference();
        return explicitConstructorMR != null ? explicitConstructorMR.getMethodName().toString()
                : getMethodCall().getProgramMethod().getName();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeSignature() throws ProofInputException {
        return createMethodReturnName(null, computeCalledMethodSignature());
    }

    /**
     * Computes the signature of the called method.
     *
     * @return The signature of the called method.
     */
    protected String computeCalledMethodSignature() throws ProofInputException {
        MethodReference explicitConstructorMR =
            getMethodCall().getExplicitConstructorMethodReference();
        String call = explicitConstructorMR != null ? explicitConstructorMR.toString()
                : getMethodCall().getMethodReference().toString();
        if (call.endsWith(";")) {
            call = call.substring(0, call.length() - 1);
        }
        return call;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getNameIncludingReturnValue() throws ProofInputException {
        if (nameIncludingReturnValue == null) {
            nameIncludingReturnValue = lazyComputeNameIncludingReturnValue();
        }
        return nameIncludingReturnValue;
    }

    /**
     * Computes the name including the return value lazily when
     * {@link #getNameIncludingReturnValue()} is called the first time.
     *
     * @return The name including the return value.
     * @throws ProofInputException
     */
    protected String lazyComputeNameIncludingReturnValue() throws ProofInputException {
        IExecutionMethodReturnValue[] returnValues = getReturnValues();
        if (returnValues.length == 0) {
            return createMethodReturnName(null, computeCalledMethodName());
        } else if (returnValues.length == 1) {
            return createMethodReturnName(returnValues[0].getName() + " ",
                computeCalledMethodName());
        } else {
            StringBuilder sb = new StringBuilder();
            sb.append('\n');
            boolean afterFirst = false;
            for (IExecutionMethodReturnValue value : returnValues) {
                if (afterFirst) {
                    sb.append(", \n");
                } else {
                    afterFirst = true;
                }
                sb.append('\t');
                sb.append(value.getName());
            }
            sb.append('\n');
            return createMethodReturnName(sb.toString(), computeCalledMethodName());
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getSignatureIncludingReturnValue() throws ProofInputException {
        if (signatureIncludingReturnValue == null) {
            signatureIncludingReturnValue = lazyComputeSigntureIncludingReturnValue();
        }
        return signatureIncludingReturnValue;
    }

    /**
     * Computes the signature including the return value lazily when
     * {@link #getNameIncludingReturnValue()} is called the first time.
     *
     * @return The name including the return value.
     * @throws ProofInputException
     */
    protected String lazyComputeSigntureIncludingReturnValue() throws ProofInputException {
        IExecutionMethodReturnValue[] returnValues = getReturnValues();
        if (returnValues.length == 0) {
            return createMethodReturnName(null, computeCalledMethodSignature());
        } else if (returnValues.length == 1) {
            return createMethodReturnName(returnValues[0].getName() + " ",
                computeCalledMethodSignature());
        } else {
            StringBuilder sb = new StringBuilder();
            sb.append('\n');
            boolean afterFirst = false;
            for (IExecutionMethodReturnValue value : returnValues) {
                if (afterFirst) {
                    sb.append(", \n");
                } else {
                    afterFirst = true;
                }
                sb.append('\t');
                sb.append(value.getName());
            }
            sb.append('\n');
            return createMethodReturnName(sb.toString(), computeCalledMethodSignature());
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IExecutionMethodReturnValue[] getReturnValues() throws ProofInputException {
        if (returnValues == null) {
            returnValues = lazyComputeReturnValues();
        }
        return returnValues;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isReturnValuesComputed() {
        return returnValues != null;
    }

    /**
     * Computes the return value lazily when {@link #getReturnValues()} is called the first time.
     *
     * @return The return value.
     * @throws ProofInputException Occurred Exception.
     */
    protected IExecutionMethodReturnValue[] lazyComputeReturnValues() throws ProofInputException {
        InitConfig initConfig = getInitConfig();
        if (initConfig != null) { // Otherwise proof is disposed.
            final Services services = initConfig.getServices();
            // Check if a result variable is available
            MethodBodyStatement mbs = getMethodCall().getActiveStatement();
            IProgramVariable resultVar = mbs.getResultVariable();
            // Create a temporary result variable for non void methods in case that it is missing in
            // method frame
            if (resultVar == null) {
                IProgramMethod pm = mbs.getProgramMethod(services);
                if (!pm.isVoid()) {
                    resultVar = new LocationVariable(
                        new ProgramElementName(services.getTermBuilder().newName("TmpResultVar")),
                        pm.getReturnType());
                }
            }
            if (resultVar != null) {
                // Search the node with applied rule "methodCallReturn" which provides the required
                // updates
                Node methodReturnNode = findMethodReturnNode(getProofNode());
                if (methodReturnNode != null) {
                    // Start site proof to extract the value of the result variable.
                    // New OneStepSimplifier is required because it has an internal state and the
                    // default instance can't be used parallel.
                    final ProofEnvironment sideProofEnv = SymbolicExecutionSideProofUtil
                            .cloneProofEnvironmentWithOwnOneStepSimplifier(getProof(), true);
                    SiteProofVariableValueInput input =
                        SymbolicExecutionUtil.createExtractReturnVariableValueSequent(services,
                            mbs.getBodySourceAsTypeReference(), mbs.getProgramMethod(services),
                            mbs.getDesignatedContext(), methodReturnNode, getProofNode(),
                            resultVar);
                    ApplyStrategyInfo<Proof, Goal> info =
                        SymbolicExecutionSideProofUtil.startSideProof(
                            getProof(), sideProofEnv, input.getSequentToProve(),
                            StrategyProperties.METHOD_NONE, StrategyProperties.LOOP_NONE,
                            StrategyProperties.QUERY_OFF, StrategyProperties.SPLITTING_NORMAL);
                    try {
                        if (info.getProof().openGoals().size() == 1) {
                            Goal goal = info.getProof().openGoals().head();
                            JTerm returnValue = SymbolicExecutionSideProofUtil
                                    .extractOperatorValue(goal, input.getOperator());
                            assert returnValue != null;
                            returnValue = SymbolicExecutionUtil
                                    .replaceSkolemConstants(goal.sequent(), returnValue, services);
                            return new IExecutionMethodReturnValue[] {
                                new ExecutionMethodReturnValue(getSettings(), getProofNode(),
                                    getModalityPIO(), returnValue, null) };
                        } else {
                            // Group equal values of different branches
                            Map<JTerm, List<Node>> valueNodeMap =
                                new LinkedHashMap<>();
                            for (Goal goal : info.getProof().openGoals()) {
                                JTerm returnValue = SymbolicExecutionSideProofUtil
                                        .extractOperatorValue(goal, input.getOperator());
                                assert returnValue != null;
                                returnValue = SymbolicExecutionUtil.replaceSkolemConstants(
                                    goal.node().sequent(), returnValue, services);
                                List<Node> nodeList = valueNodeMap.computeIfAbsent(returnValue,
                                    k -> new LinkedList<>());
                                nodeList.add(goal.node());
                            }
                            // Create result
                            if (valueNodeMap.size() == 1) {
                                JTerm returnValue = valueNodeMap.keySet().iterator().next();
                                return new IExecutionMethodReturnValue[] {
                                    new ExecutionMethodReturnValue(getSettings(), getProofNode(),
                                        getModalityPIO(), returnValue, null) };
                            } else {
                                IExecutionMethodReturnValue[] result =
                                    new IExecutionMethodReturnValue[valueNodeMap.size()];
                                int i = 0;
                                for (Entry<JTerm, List<Node>> entry : valueNodeMap.entrySet()) {
                                    List<JTerm> conditions = new LinkedList<>();
                                    for (Node node : entry.getValue()) {
                                        JTerm condition =
                                            SymbolicExecutionUtil.computePathCondition(
                                                node, getSettings().simplifyConditions(), false);
                                        conditions.add(condition);
                                    }
                                    JTerm condition = services.getTermBuilder().or(conditions);
                                    if (conditions.size() >= 2) {
                                        if (getSettings().simplifyConditions()) {
                                            condition = SymbolicExecutionUtil.simplify(initConfig,
                                                info.getProof(), condition);
                                        }
                                    }
                                    condition = SymbolicExecutionUtil.improveReadability(condition,
                                        info.getProof().getServices());
                                    result[i] = new ExecutionMethodReturnValue(getSettings(),
                                        getProofNode(), getModalityPIO(), entry.getKey(),
                                        condition);
                                    i++;
                                }
                                return result;
                            }
                        }
                    } finally {
                        SymbolicExecutionSideProofUtil
                                .disposeOrStore("Return value computation on method return node "
                                    + methodReturnNode.serialNr() + ".", info);
                    }
                } else {
                    return new IExecutionMethodReturnValue[0];
                }
            } else {
                return new IExecutionMethodReturnValue[0];
            }
        } else {
            return new IExecutionMethodReturnValue[0];
        }
    }

    /**
     * Searches from the given {@link Node} the parent which applies the rule "methodCallReturn" in
     * the same modality.
     *
     * @param node The {@link Node} to start search from.
     * @return The found {@link Node} with rule "methodCallReturn" or {@code null} if no node was
     *         found.
     */
    protected Node findMethodReturnNode(Node node) {
        Node resultNode = null;
        SymbolicExecutionTermLabel origianlLabel =
            SymbolicExecutionUtil.getSymbolicExecutionLabel(node.getAppliedRuleApp());
        if (origianlLabel != null) {
            while (node != null && resultNode == null) {
                if ("methodCallReturn".equals(MiscTools.getRuleDisplayName(node))) {
                    SymbolicExecutionTermLabel currentLabel =
                        SymbolicExecutionUtil.getSymbolicExecutionLabel(node.getAppliedRuleApp());
                    if (origianlLabel.equals(currentLabel)) {
                        resultNode = node;
                    }
                }
                node = node.parent();
            }
        }
        return resultNode;
    }

    /**
     * Creates the human readable name which is shown in {@link IExecutionMethodReturn} instances.
     *
     * @param returnValue The return value.
     * @param methodName The name of the method that is completely executed.
     * @return The created human readable name.
     */
    public static String createMethodReturnName(Object returnValue, String methodName) {
        return INTERNAL_NODE_NAME_START + "return"
            + (returnValue != null ? " " + returnValue + "as result" : "")
            + (!StringUtil.isTrimmedEmpty(methodName) ? " of " + methodName : "")
            + INTERNAL_NODE_NAME_END;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected IExecutionConstraint[] lazyComputeConstraints() {
        return SymbolicExecutionUtil.createExecutionConstraints(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getElementType() {
        return "Method Return";
    }
}
