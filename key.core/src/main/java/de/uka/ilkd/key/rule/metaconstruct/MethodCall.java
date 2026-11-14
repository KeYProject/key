/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Objects;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.abstraction.ArrayType;
import de.uka.ilkd.key.java.ast.abstraction.ClassType;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.ast.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.ast.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.expression.ArrayInitializer;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.operator.NewArray;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.FieldReference;
import de.uka.ilkd.key.java.ast.reference.IExecutionContext;
import de.uka.ilkd.key.java.ast.reference.MethodReference;
import de.uka.ilkd.key.java.ast.reference.ReferencePrefix;
import de.uka.ilkd.key.java.ast.reference.SuperReference;
import de.uka.ilkd.key.java.ast.reference.ThisReference;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.ast.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.transformations.pipeline.PipelineConstants;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Symbolically executes a method invocation.
 *
 * <p>
 * This class is intentionally {@code final}. Its {@link #transform} runs on a fresh per-call copy
 * (see there) so that the instance shared via the taclet base is never mutated and concurrent
 * method-call expansions in the parallel prover do not race on the scratch instance fields. That
 * delegation copies {@code this} by constructing a plain {@code MethodCall}; if a subclass existed
 * and overrode any of the transform helpers, the copy would silently drop the override and run the
 * wrong transformation. Forbidding subclasses keeps the copy faithful and the thread-safety
 * argument sound. Behaviour is varied through the taclet/{@link ProgramElement} arguments, not by
 * subclassing, so nothing is lost.
 */
@TransformerMeta(name = "#methodCall")
@NullMarked
public final class MethodCall extends ProgramTransformer {
    public static final Logger LOGGER = LoggerFactory.getLogger(MethodCall.class);

    private final @Nullable SchemaVariable resultVar;

    protected MethodReference methRef;
    private IProgramMethod pm;
    protected @Nullable ReferencePrefix newContext;
    protected ProgramVariable pvar;
    private final @Nullable IExecutionContext execContextSV;
    private @Nullable ExecutionContext execContext;
    protected ImmutableArray<Expression> arguments;
    protected KeYJavaType staticPrefixType;

    /**
     * creates the methodcall-MetaConstruct
     *
     * @param body the ProgramElement contained by the meta construct
     */
    public MethodCall(ProgramElement body) {
        this(null, null, body);
    }

    /**
     * Creates the methodcall-MetaConstruct with a single optional schema variable. The variable's
     * program sort decides its role: an execution-context variable is passed as the execution
     * context, a program variable as the holder of the call's result.
     *
     * @param sv the schema variable that is either the execution context or keeps the result
     * @param body the ProgramElement contained by the meta construct
     */
    public MethodCall(ProgramSV sv, ProgramElement body) {
        this(sv.sort() == ProgramSVSort.EXECUTIONCONTEXT ? sv : null,
            sv.sort() == ProgramSVSort.VARIABLE ? sv : null, body);
        if (sv.sort() != ProgramSVSort.EXECUTIONCONTEXT && sv.sort() != ProgramSVSort.VARIABLE) {
            throw new IllegalArgumentException("A single schema variable of #methodCall must be "
                + "an execution context or a result variable, but was " + sv.sort() + ".");
        }
    }

    /**
     * creates the methodcall-MetaConstruct
     *
     * @param result the SchemaVariable that is used to keep the result
     * @param body the ProgramElement contained by the meta construct
     */
    public MethodCall(@Nullable ProgramSV ec, @Nullable SchemaVariable result,
            ProgramElement body) {
        this(new Name("#methodCall"), ec, result, body);
        if (ec != null && ec.sort() != ProgramSVSort.EXECUTIONCONTEXT) {
            throw new IllegalArgumentException("The execution context of #methodCall must be "
                + "an execution-context variable, but was " + ec.sort() + ".");
        }
        if (result != null && result.sort() != ProgramSVSort.VARIABLE) {
            throw new IllegalArgumentException("The result variable of #methodCall must be "
                + "a program-variable schema variable, but was " + result.sort() + ".");
        }
    }

    /**
     * creates the methodcall-MetaConstruct
     *
     * @param result the SchemaVariable that is used to keep the result
     * @param body the ProgramElement contained by the meta construct
     * @param name Method name.
     * @param ec The Schema Variable.
     */
    // The scratch fields below (methRef, pm, newContext, pvar, execContext, arguments,
    // staticPrefixType) are filled by transformImpl before they are read; the fresh per-call
    // copy (see transform) is never exposed before that.
    @SuppressWarnings({ "NullAway", "nullness:initialization.fields.uninitialized" })
    protected MethodCall(Name name, @Nullable ProgramSV ec, @Nullable SchemaVariable result,
            ProgramElement body) {
        super(name, body);
        this.resultVar = result;
        this.execContextSV = ec;
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        final ProgramElement ec = (ProgramElement) execContextSV;
        final ProgramElement result = (ProgramElement) resultVar;
        if (ec != null) {
            return result == null ? ImmutableList.of(ec, body())
                    : ImmutableList.of(ec, result, body());
        }
        return result == null ? ImmutableList.of(body()) : ImmutableList.of(result, body());
    }

    /** gets an array of expression and returns a list of types */
    private ImmutableList<KeYJavaType> getTypes(ImmutableArray<Expression> args,
            Services services) {
        ImmutableList<KeYJavaType> result = ImmutableList.nil();
        for (int i = args.size() - 1; i >= 0; i--) {
            Expression argument = args.get(i);
            result =
                result.prepend(services.getTypeConverter().getKeYJavaType(argument, execContext));
        }
        return result;
    }

    private KeYJavaType getStaticPrefixType(@Nullable ReferencePrefix refPrefix,
            Services services) {
        if (refPrefix == null
                || refPrefix instanceof ThisReference && refPrefix.getReferencePrefix() == null) {
            return Objects.requireNonNull(Objects.requireNonNull(execContext,
                "no execution context").getTypeReference().getKeYJavaType(),
                "no KeYJavaType for the context class");
        } else if (refPrefix instanceof ThisReference) {
            ReferencePrefix nestedPrefix = Objects.requireNonNull(refPrefix.getReferencePrefix(),
                "no reference prefix in " + refPrefix);
            return Objects.requireNonNull(((TypeReference) nestedPrefix).getKeYJavaType(),
                "no KeYJavaType for " + nestedPrefix);
            // ((ProgramVariable)
            // services.getTypeConverter().convertToLogicElement(refPrefix).op()).getKeYJavaType();
        } else if (refPrefix instanceof TypeRef) {
            KeYJavaType t = ((TypeRef) refPrefix).getKeYJavaType();
            if (t == null) { // %%%
                Debug.fail();
            }
            return t;
        } else if (refPrefix instanceof ProgramVariable) {
            return Objects.requireNonNull(((ProgramVariable) refPrefix).getKeYJavaType(),
                "no KeYJavaType for " + refPrefix);
        } else if (refPrefix instanceof FieldReference) {
            return Objects.requireNonNull(
                ((FieldReference) refPrefix).getProgramVariable().getKeYJavaType(),
                "no KeYJavaType for " + refPrefix);
        } else if (refPrefix instanceof SuperReference) {
            ExecutionContext context = Objects.requireNonNull(execContext, "no execution context");
            KeYJavaType contextType = Objects.requireNonNull(
                context.getTypeReference().getKeYJavaType(),
                "no KeYJavaType for the context class");
            return Objects.requireNonNull(services.getJavaInfo().getSuperclass(contextType),
                "no superclass for " + contextType);
        } else {
            throw new IllegalArgumentException(
                "Unsupported method invocation mode\n" + refPrefix.getClass());
        }
    }

    /**
     * Returns the method.
     *
     * @param prefixType TODO
     * @param mr TODO
     * @param services TODO
     * @return TODO
     */
    protected IProgramMethod getMethod(KeYJavaType prefixType, MethodReference mr,
            Services services) {
        IProgramMethod result;
        if (execContext != null) {
            result = mr.method(services, prefixType, execContext);
            if (result == null) {
                // if a method is declared protected and prefix and
                // execContext are in different packages we have to
                // simulate visibility rules like being in prefixType
                result = mr.method(services, prefixType,
                    mr.getMethodSignature(services, execContext), prefixType);
            }
        } else {
            result = mr.method(services, prefixType, methodSignatureWithoutContext(mr, services),
                prefixType);
        }
        return Objects.requireNonNull(result, "no implementation of " + mr);
    }

    private IProgramMethod getSuperMethod(ExecutionContext ex, MethodReference mr,
            Services services) {
        return Objects.requireNonNull(mr.method(services, getSuperType(ex, services), ex),
            "no super method implementation of " + mr);
    }

    private KeYJavaType getSuperType(ExecutionContext ex, Services services) {
        KeYJavaType contextType = Objects.requireNonNull(
            ex.getTypeReference().getKeYJavaType(), "no KeYJavaType for the context class");
        return Objects.requireNonNull(services.getJavaInfo().getSuperclass(contextType),
            "no superclass for " + contextType);
    }

    /**
     * Computes a method signature without an active statement context. A {@code null} context is
     * legitimate (e.g. for invocations outside a method body); the read-only
     * {@link MethodReference} declares the parameter @NonNull although it delegates to the
     * context-tolerant type converter.
     */
    @SuppressWarnings({ "NullAway", "nullness:argument.type.incompatible" })
    private ImmutableList<KeYJavaType> methodSignatureWithoutContext(MethodReference mr,
            Services services) {
        return mr.getMethodSignature(services, null);
    }

    /**
     * Builds a method-body statement, tolerating a {@code null} receiver for static invocations.
     * {@link MethodBodyStatement} then substitutes the method's container type as context. The
     * read-only factory declares the receiver @NonNull although a static method has no receiver.
     */
    @SuppressWarnings({ "NullAway", "nullness:argument.type.incompatible" })
    private MethodBodyStatement createMethodBody(ProgramVariable result,
            @Nullable ReferencePrefix context, IProgramMethod method,
            ImmutableArray<Expression> args) {
        return KeYJavaASTFactory.methodBody(result, context, method, args);
    }

    /**
     * Performs the program transformation needed for symbolic program execution.
     *
     * <p>
     * The actual work ({@link #transformImpl}) fills several scratch instance fields. Because this
     * transformer object is part of the shared taclet base, running it on {@code this} would race
     * across concurrent workers (the parallel prover). We therefore run on a fresh, per-call copy:
     * its scratch fields are confined to this invocation, and it is throwaway state &mdash; never
     * inserted into any AST. (MethodCall has no subclasses, so the copy faithfully replaces this.)
     *
     * @param services the Services with all necessary information about the java programs
     * @param svInst the instantiations esp. of the inner and outer label
     * @return the transformed program
     */
    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        return new MethodCall((ProgramSV) execContextSV, resultVar, body())
                .transformImpl(pe, services, svInst);
    }

    private ProgramElement[] transformImpl(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        LOGGER.trace("#methodCall: called for {}", pe);
        if (resultVar != null) {
            pvar = (ProgramVariable) Objects.requireNonNull(svInst.getInstantiation(resultVar),
                "no instantiation of " + resultVar);
        }

        execContext = execContextSV == null
                ? Objects.requireNonNull(svInst.getContextInstantiation(),
                    "no context instantiation").activeStatementContext()
                : (ExecutionContext) svInst.getInstantiation((SchemaVariable) execContextSV);
        methRef = (MethodReference) pe;

        ReferencePrefix refPrefix = methRef.getReferencePrefix();
        if (refPrefix == null) {
            ExecutionContext currentContext =
                Objects.requireNonNull(execContext, "no execution context");
            if (currentContext.getRuntimeInstance() == null) {
                refPrefix = currentContext.getTypeReference();
            } else {
                refPrefix = currentContext.getRuntimeInstance();
            }
        }

        staticPrefixType = getStaticPrefixType(methRef.getReferencePrefix(), services);
        pm = Objects.requireNonNull(execContext == null
                ? methRef.method(services, staticPrefixType,
                    methodSignatureWithoutContext(methRef, services), staticPrefixType)
                : methRef.method(services, staticPrefixType, execContext),
            "methodcall:No implementation available for " + methRef);

        newContext = methRef.getReferencePrefix();
        if (newContext == null) {
            JTerm self = services.getTypeConverter().findThisForSort(Objects.requireNonNull(
                Objects.requireNonNull(pm.getContainerType(), "no container type for " + pm)
                        .getSort(),
                "no sort for the container type"), execContext);
            if (self != null) {
                newContext = (ReferencePrefix) services.getTypeConverter()
                        .convertToProgramElement(self);
            }
        } else if (newContext instanceof ThisReference thisRef) {
            newContext = (ReferencePrefix) services.getTypeConverter().convertToProgramElement(
                services.getTypeConverter().convertToLogicElement(thisRef, execContext));
        } else if (newContext instanceof FieldReference fieldContext) {
            if (fieldContext.referencesOwnInstanceField()) {
                newContext = fieldContext.setReferencePrefix(Objects.requireNonNull(
                    Objects.requireNonNull(execContext, "no execution context")
                            .getRuntimeInstance(),
                    "no runtime instance in execution context"));
            }
        }

        VariableSpecification[] paramSpecs = createParamSpecs(services);
        Statement[] paramDecl = createParamAssignments(paramSpecs);
        arguments = getVariables(paramSpecs);

        Statement result = null;
        if (pm.isStatic()) { // Static invocation mode
            result = handleStatic(services);
        } else if (refPrefix instanceof SuperReference) {
            result = handleSuperReference(services);
        } else { // Instance invocation mode
            result = handleInstanceInvocation(services);
        }
        return new ProgramElement[] {
            KeYJavaASTFactory.insertStatementInBlock(paramDecl, KeYJavaASTFactory.block(result)) };
    }

    private Statement handleStatic(Services services) {
        Statement result;
        LOGGER.trace("#methodCall: invocation of static method detected");
        newContext = null;
        IProgramMethod staticMethod = getMethod(staticPrefixType, methRef, services);
        result = createMethodBody(pvar, newContext, staticMethod, arguments);
        return result;
    }

    private Statement handleSuperReference(Services services) {
        Statement result;
        LOGGER.trace(
            "#methodCall: super invocation of method detected." + "Requires static resolving.");
        ExecutionContext ex = Objects.requireNonNull(execContext, "no execution context");
        IProgramMethod superMethod = getSuperMethod(ex, methRef, services);
        result = KeYJavaASTFactory.methodBody(pvar,
            Objects.requireNonNull(ex.getRuntimeInstance(),
                "no runtime instance in execution context"),
            superMethod, arguments);
        return result;
    }

    private Statement handleInstanceInvocation(Services services) {
        Statement result = null;
        if (pm.isPrivate() || (methRef.implicit() && Objects.requireNonNull(methRef.getName(),
            "no method name in " + methRef)
                .equals(PipelineConstants.CONSTRUCTOR_NORMALFORM_IDENTIFIER))) {
            // private methods or constructor invocations are bound
            // statically
            LOGGER.trace("#methodCall: invocation of private method detected."
                + "Requires static resolving.");
            result = makeMbs(staticPrefixType, services);
        } else {
            LOGGER.trace("#methodCall: invocation of non-private" + " instance method detected."
                + "Requires dynamic resolving.");
            ImmutableList<KeYJavaType> imps =
                services.getJavaInfo().getKeYProgModelInfo().findImplementations(staticPrefixType,
                    Objects.requireNonNull(methRef.getName(), "no method name in " + methRef),
                    getTypes(arguments, services));
            if (imps.isEmpty()) {
                imps = services.getJavaInfo().getKeYProgModelInfo().findImplementations(
                    Objects.requireNonNull(pm.getContainerType(), "no container type for " + pm),
                    Objects.requireNonNull(methRef.getName(), "no method name in " + methRef),
                    getTypes(arguments, services));
            }
            if (imps.isEmpty()) {
                Type staticPrefix = staticPrefixType.getJavaType();
                if (staticPrefix instanceof ClassType && (((ClassType) staticPrefix).isInterface()
                        || ((ClassType) staticPrefix).isAbstract())) {
                    // no implementing sub type found
                    // insert mbs with interface type so that contracts are
                    // applicable
                    result = makeMbs(staticPrefixType, services);
                }
            } else {
                result = makeIfCascade(imps, services);
            }
        }
        return Objects.requireNonNull(result, "no implementation to dispatch to for " + methRef);
    }

    // ***************** Dynamic Binding Construction Utilities ***************

    private Statement makeMbs(KeYJavaType t, Services services) {
        Statement result;
        IProgramMethod meth = getMethod(t, methRef, services);

        // Add a down cast if the programvariable is of a supertype
        // bugfix for #1226 (first bugfix was in expand, but moved here and
        // modified it to avoid incompleteness issues)
        if (!meth.isStatic()) {
            ReferencePrefix localContext = Objects.requireNonNull(newContext,
                "no invocation target for " + meth);
            final Expression newContextAsExp = (Expression) localContext;

            LocalVariableDeclaration castedThisVar = null;
            final KeYJavaType targetType = Objects.requireNonNull(meth.getContainerType(),
                "no container type for " + meth);
            if (newContextAsExp.getKeYJavaType(services, execContext) != targetType) {
                castedThisVar = KeYJavaASTFactory.declare(
                    new ProgramElementName(services.getTermBuilder().newName("target")),
                    KeYJavaASTFactory.cast(newContextAsExp, targetType), new TypeRef(targetType));

                localContext = (ReferencePrefix) castedThisVar.getVariableSpecifications().get(0)
                        .getProgramVariable();
            }

            result = KeYJavaASTFactory.methodBody(pvar, localContext, meth, arguments);
            if (castedThisVar != null) {
                result = KeYJavaASTFactory.block(castedThisVar, result);
            }

        } else {
            result = createMethodBody(pvar, newContext, meth, arguments);
        }
        return result;

    }

    private Expression makeIOf(Type t) {
        return KeYJavaASTFactory.instanceOf(
            (Expression) Objects.requireNonNull(newContext, "no receiver for the dispatch test"),
            (KeYJavaType) t);
    }

    /**
     * TODO
     *
     * @param imps TODO
     * @param services The Services object.
     * @return TODO
     */
    protected Statement makeIfCascade(ImmutableList<KeYJavaType> imps, Services services) {
        KeYJavaType currType = imps.head();
        if (imps.size() == 1) {
            return makeMbs(currType, services);
        } else {
            return KeYJavaASTFactory.ifElse(makeIOf(currType), makeMbs(currType, services),
                makeIfCascade(imps.tail(), services));
        }
    }

    private VariableSpecification[] createParamSpecs(Services services) {

        MethodDeclaration methDecl =
            Objects.requireNonNull(pm.getMethodDeclaration(), "no method declaration for " + pm);
        int params = methDecl.getParameterDeclarationCount();
        VariableSpecification[] varSpecs = new VariableSpecification[params];
        for (int i = 0; i < params; i++) {
            ParameterDeclaration parDecl = methDecl.getParameterDeclarationAt(i);
            VariableSpecification originalSpec = parDecl.getVariableSpecification();
            final ProgramVariable originalParamVar =
                (ProgramVariable) originalSpec.getProgramVariable();

            final IProgramVariable paramVar = KeYJavaASTFactory.localVariable(services,
                originalParamVar.getProgramElementName().toString(),
                Objects.requireNonNull(originalParamVar.getTypeReference(),
                    "no type reference for " + originalParamVar));

            // this condition checks whether this is the last formal parameter
            // and is used
            // in the context of a method with a variable number of args.
            // see makeVariableArgument below
            if (i == params - 1 && methDecl.isVarArgMethod()
                    && (methRef.getArguments().size() != params
                            || !assignmentCompatible(methRef.getArgumentAt(i),
                                originalSpec.getType(), services))) {
                // variable argument
                varSpecs[i] = KeYJavaASTFactory.variableSpecification(paramVar, 1,
                    makeVariableArgument(originalSpec), originalSpec.getType());
            } else {
                // normal argument
                varSpecs[i] = KeYJavaASTFactory.variableSpecification(paramVar,
                    originalSpec.getDimensions(), methRef.getArgumentAt(i), originalSpec.getType());
            }
        }
        return varSpecs;
    }

    /**
     * make an array out of a list of arguments to a method with variable arguments.
     *
     * <pre>
     * Quote JLS 15.12.4.2 Evaluate Arguments The process of evaluating of the
     * argument list differs, depending on whether the method being invoked is a
     * fixed arity method or a variable arity method (JLS 8.4.1).
     *
     * If the method being invoked is a variable arity method (JLS 8.4.1) m, it
     * necessarily has n>0 formal parameters. The final formal parameter of m
     * necessarily has type T[] for some T, and m is necessarily being invoked
     * with k0 actual argument expressions.
     *
     * If m is being invoked with kn actual argument expressions, or, if m is
     * being invoked with k=n actual argument expressions and the type of the
     * kth argument expression is not assignment compatible with T[], then the
     * argument list (e1, ... , en-1, en, ...ek) is evaluated as if it were
     * written as (e1, ..., en-1, new T[]{en, ..., ek}).
     * </pre>
     *
     * Thus, when the last formal parameter is reached and circumstances enforce wrapping arguments
     * in an array, this method creates the expected.
     *
     * @author MU
     * @since 2008-Mar
     *
     *        see examples/java_dl/java5/vararg.key for examples and tests.
     *
     * @param originalSpec the original sepcification of the formal paramater
     * @return an Newarray expression conglomerating all remaining arguments may be zero.
     */
    private Expression makeVariableArgument(VariableSpecification originalSpec) {

        int params = Objects.requireNonNull(pm.getMethodDeclaration(),
            "no method declaration for " + pm).getParameterDeclarationCount();
        int args = methRef.getArguments().size();
        Expression[] exps = new Expression[args - params + 1];

        for (int i = 0; i < exps.length; i++) {
            exps[i] = methRef.getArgumentAt(params - 1 + i);
        }

        Type type = originalSpec.getType();

        // for some reason this does not work, but type itself is a KJT ???
        // KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(type);
        KeYJavaType kjt = (KeYJavaType) type;
        ArrayType arrayTy =
            (ArrayType) Objects.requireNonNull(kjt.getJavaType(), "no array type for " + kjt);

        TypeReference baseTyRef = arrayTy.getBaseType();

        ArrayInitializer arrayInit = KeYJavaASTFactory.arrayInitializer(exps, kjt);
        NewArray newArray = KeYJavaASTFactory.newArray(baseTyRef, 1, arrayInit, kjt);

        return newArray;
    }

    private Statement[] createParamAssignments(VariableSpecification[] specs) {
        MethodDeclaration methDecl =
            Objects.requireNonNull(pm.getMethodDeclaration(), "no method declaration for " + pm);
        Statement[] paramDecl = new Statement[specs.length];
        for (int i = 0; i < specs.length; i++) {
            ParameterDeclaration parDecl = methDecl.getParameterDeclarationAt(i);
            paramDecl[i] = KeYJavaASTFactory.declare(parDecl.getModifiers(),
                Objects.requireNonNull(parDecl.getTypeReference(),
                    "no type reference for " + parDecl),
                specs[i]);
        }
        return paramDecl;
    }

    private ImmutableArray<Expression> getVariables(VariableSpecification[] varspecs) {
        Expression[] vars = new Expression[varspecs.length];
        for (int i = 0; i < varspecs.length; i++) {
            vars[i] = (Expression) varspecs[i].getProgramVariable();
        }
        return new ImmutableArray<>(vars);
    }

    /**
     * check whether an expression is assignment-compatible with the array over a type.
     *
     * Quoting JLS: 15.12.4.2 Evaluate Arguments
     *
     * "if m is being invoked with k=n actual argument expressions and the type of the kth argument
     * expression is not assignment compatible with T[], then the argument list"
     *
     * In the absence of autoboxing this is the case if the type is a subtype.
     *
     * @param exp expression to check
     * @param type type to check for
     * @return true iff exp is assign compatible with type
     */
    private boolean assignmentCompatible(Expression exp, Type type, Services services) {
        KeYJavaType expKjt = Objects.requireNonNull(exp.getKeYJavaType(services, execContext),
            "no KeYJavaType for " + exp);
        Sort expSort = Objects.requireNonNull(expKjt.getSort(), "no sort for " + expKjt);
        Sort typeSort =
            Objects.requireNonNull(((KeYJavaType) type).getSort(), "no sort for " + type);
        /* was: services.getJavaInfo().getKeYJavaType(type); */
        return expSort.extendsTrans(typeSort);
    }
}
