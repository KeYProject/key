/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBaseMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.KeYTypeUtil;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * The default implementation of {@link IExecutionMethodCall}.
 *
 * @author Martin Hentschel
 */
public class ExecutionMethodCall extends AbstractExecutionNode<MethodBodyStatement>
        implements IExecutionMethodCall {
    /**
     * The up to know discovered {@link IExecutionBaseMethodReturn}s.
     */
    private ImmutableList<IExecutionBaseMethodReturn<?>> methodReturns = ImmutableSLList.nil();

    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     */
    public ExecutionMethodCall(ITreeSettings settings, Node proofNode) {
        super(settings, proofNode);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeName() {
        return INTERNAL_NODE_NAME_START + "call " + getMethodCallText() + INTERNAL_NODE_NAME_END;
    }

    /**
     * Computes the method call text.
     *
     * @return The method call text.
     */
    protected String getMethodCallText() {
        MethodReference explicitConstructorMR = getExplicitConstructorMethodReference();
        String call = explicitConstructorMR != null ? explicitConstructorMR.toString()
                : getMethodReference().toString();
        if (call.endsWith(";")) {
            call = call.substring(0, call.length() - 1);
        }
        return call;
    }

    /**
     * Removes the given {@link IExecutionBaseMethodReturn}.
     *
     * @param methodReturn The {@link IExecutionBaseMethodReturn} to be deleted.
     * @author Anna Filighera
     */
    public void removeMethodReturn(IExecutionBaseMethodReturn<?> methodReturn) {
        methodReturns = methodReturns.removeAll(methodReturn);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isImplicitConstructor() {
        return KeYTypeUtil.isImplicitConstructor(getProgramMethod());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MethodReference getExplicitConstructorMethodReference() {
        IProgramMethod explicitConstructor = getExplicitConstructorProgramMethod();
        if (explicitConstructor != null) {
            MethodReference mr = getMethodReference();
            return new MethodReference(mr.getArguments(),
                explicitConstructor.getProgramElementName(), null); // Ignore the prefix because it
                                                                    // is ugly if a constructor is
                                                                    // called on an object not part
                                                                    // of the symbolic execution
                                                                    // tree.
        } else {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IProgramMethod getExplicitConstructorProgramMethod() {
        IProgramMethod pm = getProgramMethod();
        if (KeYTypeUtil.isImplicitConstructor(pm)) {
            return KeYTypeUtil.findExplicitConstructor(getServices(), pm);
        } else {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MethodReference getMethodReference() {
        return getActiveStatement().getMethodReference();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IProgramMethod getProgramMethod() {
        return getActiveStatement().getProgramMethod(getServices());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getElementType() {
        return "Method Call";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<IExecutionBaseMethodReturn<?>> getMethodReturns() {
        return methodReturns;
    }

    /**
     * Registers the given {@link IExecutionBaseMethodReturn}.
     *
     * @param methodReturn The {@link IExecutionBaseMethodReturn} to register.
     */
    public void addMethodReturn(IExecutionBaseMethodReturn<?> methodReturn) {
        if (methodReturn != null) {
            assert methodReturn.getMethodCall() == this;
            methodReturns = methodReturns.append(methodReturn);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected IExecutionConstraint[] lazyComputeConstraints() {
        return SymbolicExecutionUtil.createExecutionConstraints(this);
    }
}
