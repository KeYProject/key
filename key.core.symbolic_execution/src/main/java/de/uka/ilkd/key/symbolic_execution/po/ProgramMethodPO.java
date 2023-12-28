/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.po;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.pp.PrettyPrinter;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.Context;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Properties;

/**
 * <p>
 * This proof obligation executes an {@link IProgramMethod} with an optional precondition.
 * </p>
 * <p>
 * The generated {@link Sequent} has the following form:
 *
 * <pre>
 * {@code
 * ==>
 * <generalAssumptions> &
 * <preconditions>
 * ->
 * <updatesToStoreInitialValues>
 * <modalityStart>
 * exc=null;
 * try {
 *   <methodBodyStatement>
 * } catch(java.lang.Exception e) {
 *    exc = e
 * }
 * <modalityEnd>
 *  (exc = null & <postconditions > & <optionalUninterpretedPredicate>)
 * }
 * </pre>
 * </p>
 *
 * @author Martin Hentschel
 */
public class ProgramMethodPO extends AbstractOperationPO {
    /**
     * The {@link IProgramMethod} to execute code parts from.
     */
    private final IProgramMethod pm;

    /**
     * The precondition in JML syntax.
     */
    private final String precondition;

    /**
     * Constructor.
     *
     * @param initConfig   The {@link InitConfig} to use.
     * @param name         The name to use.
     * @param pm           The {@link IProgramMethod} to execute code parts from.
     * @param precondition An optional precondition to use.
     */
    public ProgramMethodPO(InitConfig initConfig, String name, IProgramMethod pm,
                           String precondition) {
        super(initConfig, name);
        assert pm != null;
        this.pm = pm;
        this.precondition = precondition;
    }

    /**
     * Constructor.
     *
     * @param initConfig                The {@link InitConfig} to use.
     * @param name                      The name to use.
     * @param pm                        The {@link IProgramMethod} to execute code parts from.
     * @param precondition              An optional precondition to use.
     * @param addUninterpretedPredicate {@code true} postcondition contains uninterpreted predicate,
     *                                  {@code false} uninterpreted predicate is not contained in postcondition.
     * @param addSymbolicExecutionLabel {@code true} to add the {@link SymbolicExecutionTermLabel}
     *                                  to the modality, {@code false} to not label the modality.
     */
    public ProgramMethodPO(InitConfig initConfig, String name, IProgramMethod pm,
                           String precondition, boolean addUninterpretedPredicate,
                           boolean addSymbolicExecutionLabel) {
        super(initConfig, name, addUninterpretedPredicate, addSymbolicExecutionLabel);
        assert pm != null;
        this.pm = pm;
        this.precondition = precondition;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IProgramMethod getProgramMethod() {
        return pm;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected boolean isTransactionApplicable() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected KeYJavaType getCalleeKeYJavaType() {
        return pm.getContainerType();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected ImmutableList<StatementBlock> buildOperationBlocks(
            ImmutableList<LocationVariable> formalParVars, ProgramVariable selfVar,
            ProgramVariable resultVar, Services services) {
        // Get program method to execute
        IProgramMethod pm = getProgramMethod();
        // Extracts code parts of the method
        ImmutableArray<Expression> args = new ImmutableArray<>(
                formalParVars.toArray(new ProgramVariable[formalParVars.size()]));
        MethodBodyStatement mbs = new MethodBodyStatement(pm, selfVar, resultVar, args);
        StatementBlock result = new StatementBlock(mbs);
        return ImmutableSLList.<StatementBlock>nil().prepend(null, result, null, null);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Term generateMbyAtPreDef(ProgramVariable selfVar,
                                       ImmutableList<ProgramVariable> paramVars, Services services) {
        return tb.tt();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Term getPre(List<LocationVariable> modHeaps, ProgramVariable selfVar,
                          ImmutableList<ProgramVariable> paramVars,
                          Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        if (precondition != null && !precondition.isEmpty()) {
            var context = Context.inMethod(getProgramMethod(), services.getTermBuilder());
            JmlIO io = new JmlIO(services).context(context).parameters(paramVars);

            PositionedString ps = new PositionedString(precondition);
            return io.parseExpression(ps);
        } else {
            return tb.tt();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Term getPost(List<LocationVariable> modHeaps, ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
                           ProgramVariable exceptionVar, Map<LocationVariable, LocationVariable> atPreVars,
                           Services services) {
        return tb.tt();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Term buildFrameClause(List<LocationVariable> modHeaps, Map<Term, Term> heapToAtPre,
                                    ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars, Services services) {
        return tb.tt();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Modality getTerminationMarker() {
        return Modality.DIA;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected boolean isMakeNamesUnique() {
        return false; // Unique names crashes precondition parsing if names are renamed.
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected boolean isCopyOfMethodArgumentsUsed() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String buildPOName(boolean transactionFlag) {
        return name;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return pm.hashCode() + (precondition != null ? precondition.hashCode() : 0);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(Object obj) {
        if (obj instanceof ProgramMethodPO other) {
            return Objects.equals(pm, other.getProgramMethod())
                    && Objects.equals(precondition, other.getPrecondition());
        } else {
            return false;
        }
    }

    /**
     * Returns the precondition in JML syntax.
     *
     * @return The precondition in JML syntax.
     */
    public String getPrecondition() {
        return precondition;
    }

    /**
     * {@inheritDoc}
     *
     * @return
     */
    @Override
    public Configuration createLoaderConfig() {
        var c = super.createLoaderConfig();
        c.set("method", getProgramMethodSignature(getProgramMethod(), true));
        if (getPrecondition() != null && !getPrecondition().isEmpty()) {
            c.set("precondition", getPrecondition());
        }
        return c;
    }

    /**
     * Returns a human-readable full qualified method signature.
     *
     * @param pm          The {@link IProgramMethod} which provides the signature.
     * @param includeType Include the container type?
     * @return The human-readable method signature.
     */
    public static String getProgramMethodSignature(IProgramMethod pm, boolean includeType) {
        PosTableLayouter l = PosTableLayouter.pure();
        l.beginC(0);
        if (includeType) {
            KeYJavaType type = pm.getContainerType();
            l.print(type.getFullName());
            l.print("#");
        }
        PrettyPrinter x = new PrettyPrinter(l);
        x.writeFullMethodSignature(pm);
        l.end();
        return x.result();
    }

    /**
     * Searches the {@link IProgramMethod} defined by the given {@link Properties}.
     *
     * @param initConfig The already loaded {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The found {@link IProgramMethod}.
     * @throws IOException Occurred Exception if it was not possible to find the
     *                     {@link IProgramMethod}.
     */
    public static IProgramMethod getProgramMethod(InitConfig initConfig, Configuration properties)
            throws IOException {
        // Get container class and method signature
        String value = properties.getString("method");
        if (value == null) {
            throw new IOException("Property \"method\" is not defined.");
        }
        int classMethodSeparator = value.indexOf("#");
        if (classMethodSeparator < 0) {
            throw new IOException(
                    "Property \"method\" does not contain the class method separator \"#\".");
        }
        String className = value.substring(0, classMethodSeparator);
        String signature = value.substring(classMethodSeparator + 1);
        JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
        // Split signature in name and parameter type names
        int breaketsStart = signature.indexOf("(");
        if (breaketsStart < 0) {
            throw new IOException("Method signature \"" + signature
                    + "\" does not contain required character \"(\".");
        }
        int breaketsEnd = signature.lastIndexOf(")");
        if (breaketsEnd < 0) {
            throw new IOException("Method signature \"" + signature
                    + "\" does not contain required character \")\".");
        }
        if (breaketsEnd < breaketsStart) {
            throw new IOException(
                    "Method signature has not valid order of chracters \"(\" and \")\".");
        }
        String name = signature.substring(0, breaketsStart);
        String parameters = signature.substring(breaketsStart + 1, breaketsEnd);
        String[] types = parameters.isEmpty() ? new String[0] : parameters.split(",");
        // Find container and parameter types
        KeYJavaType type = javaInfo.getKeYJavaType(className.trim());
        if (type == null) {
            throw new IOException("Can't find type \"" + className + "\".");
        }
        ImmutableList<KeYJavaType> parameterTypes = ImmutableSLList.nil();
        for (String s : types) {
            KeYJavaType paramType = javaInfo.getKeYJavaType(s.trim());
            if (paramType == null) {
                throw new IOException("Can't find type \"" + s + "\".");
            }
            parameterTypes = parameterTypes.append(paramType);
        }
        IProgramMethod pm = javaInfo.getProgramMethod(type, name.trim(), parameterTypes, type);
        if (pm == null) {
            pm = javaInfo.getConstructor(type, parameterTypes);
            if (pm == null) {
                throw new IOException("Can't find program method \"" + value + "\".");
            }
        }
        return pm;
    }

    /**
     * Returns the optional defined precondition.
     *
     * @param properties The proof obligation settings to read from.
     * @return The precondition or {@code null} if not available.
     */
    public static String getPrecondition(Configuration properties) {
        return properties.getString("precondition");
    }

    @Override
    protected Term getGlobalDefs(LocationVariable heap, Term heapTerm, Term selfTerm,
                                 ImmutableList<Term> paramTerms, Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public KeYJavaType getContainerType() {
        return getProgramMethod().getContainerType();
    }
}
