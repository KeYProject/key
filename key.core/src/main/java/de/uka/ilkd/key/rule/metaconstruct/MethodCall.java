/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Symbolically executes a method invocation
 */
public class MethodCall extends ProgramTransformer {
    public static final Logger LOGGER = LoggerFactory.getLogger(MethodCall.class);

    private final SchemaVariable resultVar;

    protected MethodReference methRef;
    private IProgramMethod pm;
    protected ReferencePrefix newContext;
    protected ProgramVariable pvar;
    private final IExecutionContext execContextSV;
    private ExecutionContext execContext;
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
     * creates the methodcall-MetaConstruct
     *
     * @param result the SchemaVariable that is used to keep the result
     * @param body the ProgramElement contained by the meta construct
     */
    public MethodCall(SchemaVariable result, ProgramElement body) {
        this(null, result, body);
    }

    /**
     * creates the methodcall-MetaConstruct
     *
     * @param result the SchemaVariable that is used to keep the result
     * @param body the ProgramElement contained by the meta construct
     */
    public MethodCall(ProgramSV ec, SchemaVariable result, ProgramElement body) {
        this(new Name("method-call"), ec, result, body);
    }

    /**
     * creates the methodcall-MetaConstruct
     *
     * @param result the SchemaVariable that is used to keep the result
     * @param body the ProgramElement contained by the meta construct
     * @param name Method name.
     * @param ec The Schema Variable.
     */
    protected MethodCall(Name name, ProgramSV ec, SchemaVariable result, ProgramElement body) {
        super(name, body);
        this.resultVar = result;
        this.execContextSV = ec;
    }

    /** gets an array of expression and returns a list of types */
    private ImmutableList<KeYJavaType> getTypes(ImmutableArray<Expression> args,
            Services services) {
        ImmutableList<KeYJavaType> result = ImmutableSLList.nil();
        for (int i = args.size() - 1; i >= 0; i--) {
            Expression argument = args.get(i);
            result =
                result.prepend(services.getTypeConverter().getKeYJavaType(argument, execContext));
        }
        return result;
    }

    private KeYJavaType getStaticPrefixType(ReferencePrefix refPrefix, Services services) {
        if (refPrefix == null
                || refPrefix instanceof ThisReference && refPrefix.getReferencePrefix() == null) {
            return execContext.getTypeReference().getKeYJavaType();
        } else if (refPrefix instanceof ThisReference) {
            return ((TypeReference) refPrefix.getReferencePrefix()).getKeYJavaType();
            // ((ProgramVariable)
            // services.getTypeConverter().convertToLogicElement(refPrefix).op()).getKeYJavaType();
        } else if (refPrefix instanceof TypeRef) {
            KeYJavaType t = ((TypeRef) refPrefix).getKeYJavaType();
            if (t == null) { // %%%
                Debug.fail();
            }
            return t;
        } else if (refPrefix instanceof ProgramVariable) {
            return ((ProgramVariable) refPrefix).getKeYJavaType();
        } else if (refPrefix instanceof FieldReference) {
            return ((FieldReference) refPrefix).getProgramVariable().getKeYJavaType();
        } else if (refPrefix instanceof SuperReference) {
            KeYJavaType st = services.getJavaInfo()
                    .getSuperclass(execContext.getTypeReference().getKeYJavaType());
            return st;
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
            result = mr.method(services, prefixType, mr.getMethodSignature(services, execContext),
                prefixType);
        }
        return result;
    }

    private IProgramMethod getSuperMethod(ExecutionContext ex, MethodReference mr,
            Services services) {
        return mr.method(services, getSuperType(ex, services), ex);
    }

    private KeYJavaType getSuperType(ExecutionContext ex, Services services) {
        return services.getJavaInfo().getSuperclass(ex.getTypeReference().getKeYJavaType());
    }

    /**
     * performs the program transformation needed for symbolic program execution
     *
     * @param services the Services with all necessary information about the java programs
     * @param svInst the instantiations esp. of the inner and outer label
     * @return the transformed program
     */
    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        LOGGER.trace("method-call: called for {}", pe);
        if (resultVar != null) {
            pvar = (ProgramVariable) svInst.getInstantiation(resultVar);
        }

        execContext =
            execContextSV == null ? svInst.getContextInstantiation().activeStatementContext()
                    : (ExecutionContext) svInst.getInstantiation((SchemaVariable) execContextSV);
        methRef = (MethodReference) pe;

        ReferencePrefix refPrefix = methRef.getReferencePrefix();
        if (refPrefix == null) {
            if (execContext.getRuntimeInstance() == null) {
                refPrefix = execContext.getTypeReference();
            } else {
                refPrefix = execContext.getRuntimeInstance();
            }
        }

        staticPrefixType = getStaticPrefixType(methRef.getReferencePrefix(), services);
        pm = execContext == null
                ? methRef.method(services, staticPrefixType,
                    methRef.getMethodSignature(services, null), staticPrefixType)
                : methRef.method(services, staticPrefixType, execContext);
        if (pm == null) {
            Debug.fail("methodcall:No implementation available for ", methRef);
        }

        newContext = methRef.getReferencePrefix();
        if (newContext == null) {
            Term self = services.getTypeConverter().findThisForSort(pm.getContainerType().getSort(),
                execContext);
            if (self != null) {
                newContext =
                    (ReferencePrefix) services.getTypeConverter().convertToProgramElement(self);
            }
        } else if (newContext instanceof ThisReference) {
            newContext = (ReferencePrefix) services.getTypeConverter().convertToProgramElement(
                services.getTypeConverter().convertToLogicElement(newContext, execContext));
        } else if (newContext instanceof FieldReference) {
            final FieldReference fieldContext = (FieldReference) newContext;
            if (fieldContext.referencesOwnInstanceField()) {
                newContext = fieldContext.setReferencePrefix(execContext.getRuntimeInstance());
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
            result = handleInstanceInvocation(services, result);
        }
        return new ProgramElement[] {
            KeYJavaASTFactory.insertStatementInBlock(paramDecl, KeYJavaASTFactory.block(result)) };
    }

    private Statement handleStatic(Services services) {
        Statement result;
        LOGGER.trace("method-call: invocation of static method detected");
        newContext = null;
        IProgramMethod staticMethod = getMethod(staticPrefixType, methRef, services);
        result = KeYJavaASTFactory.methodBody(pvar, newContext, staticMethod, arguments);
        return result;
    }

    private Statement handleSuperReference(Services services) {
        Statement result;
        LOGGER.trace(
            "method-call: super invocation of method detected." + "Requires static resolving.");
        IProgramMethod superMethod = getSuperMethod(execContext, methRef, services);
        result = KeYJavaASTFactory.methodBody(pvar, execContext.getRuntimeInstance(), superMethod,
            arguments);
        return result;
    }

    private Statement handleInstanceInvocation(Services services, Statement result) {
        if (pm.isPrivate() || (methRef.implicit() && methRef.getName()
                .equals(ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER))) {
            // private methods or constructor invocations are bound
            // statically
            LOGGER.trace("method-call: invocation of private method detected."
                + "Requires static resolving.");
            result = makeMbs(staticPrefixType, services);
        } else {
            LOGGER.trace("method-call: invocation of non-private" + " instance method detected."
                + "Requires dynamic resolving.");
            ImmutableList<KeYJavaType> imps =
                services.getJavaInfo().getKeYProgModelInfo().findImplementations(staticPrefixType,
                    methRef.getName(), getTypes(arguments, services));
            if (imps.isEmpty()) {
                imps = services.getJavaInfo().getKeYProgModelInfo().findImplementations(
                    pm.getContainerType(), methRef.getName(), getTypes(arguments, services));
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
        return result;
    }

    // ***************** Dynamic Binding Construction Utilities ***************

    private Statement makeMbs(KeYJavaType t, Services services) {
        Statement result;
        IProgramMethod meth = getMethod(t, methRef, services);

        // Add a down cast if the programvariable is of a supertype
        // bugfix for #1226 (first bugfix was in expand, but moved here and
        // modified it to avoid incompleteness issues)
        if (!meth.isStatic()) {

            final Expression newContextAsExp = (Expression) newContext;
            ReferencePrefix localContext = newContext;

            LocalVariableDeclaration castedThisVar = null;
            final KeYJavaType targetType = meth.getContainerType();
            if (newContextAsExp.getKeYJavaType(services, execContext) != targetType) {
                castedThisVar = KeYJavaASTFactory.declare(
                    new ProgramElementName(services.getTermBuilder().newName("target")),
                    KeYJavaASTFactory.cast(newContextAsExp, targetType), targetType);

                localContext = (ReferencePrefix) castedThisVar.getVariableSpecifications().get(0)
                        .getProgramVariable();
            }

            result = KeYJavaASTFactory.methodBody(pvar, localContext, meth, arguments);
            if (castedThisVar != null) {
                result = KeYJavaASTFactory.block(castedThisVar, result);
            }

        } else {
            result = KeYJavaASTFactory.methodBody(pvar, newContext, meth, arguments);
        }
        return result;

    }

    private Expression makeIOf(Type t) {
        Debug.assertTrue(newContext != null);
        return KeYJavaASTFactory.instanceOf((Expression) newContext, (KeYJavaType) t);
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

        MethodDeclaration methDecl = pm.getMethodDeclaration();
        int params = methDecl.getParameterDeclarationCount();
        VariableSpecification[] varSpecs = new VariableSpecification[params];
        for (int i = 0; i < params; i++) {
            ParameterDeclaration parDecl = methDecl.getParameterDeclarationAt(i);
            VariableSpecification originalSpec = parDecl.getVariableSpecification();
            final ProgramVariable originalParamVar =
                (ProgramVariable) originalSpec.getProgramVariable();

            final IProgramVariable paramVar = KeYJavaASTFactory.localVariable(services,
                originalParamVar.getProgramElementName().toString(),
                originalParamVar.getKeYJavaType());

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

        int params = pm.getMethodDeclaration().getParameterDeclarationCount();
        int args = methRef.getArguments().size();
        Expression[] exps = new Expression[args - params + 1];

        for (int i = 0; i < exps.length; i++) {
            exps[i] = methRef.getArgumentAt(params - 1 + i);
        }

        Type type = originalSpec.getType();

        // for some reason this does not work, but type itself is a KJT ???
        // KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(type);
        KeYJavaType kjt = (KeYJavaType) type;
        ArrayType arrayTy = (ArrayType) kjt.getJavaType();

        TypeReference baseTyRef = arrayTy.getBaseType();

        ArrayInitializer arrayInit = KeYJavaASTFactory.arrayInitializer(exps, kjt);
        NewArray newArray = KeYJavaASTFactory.newArray(baseTyRef, 1, arrayInit, kjt);

        return newArray;
    }

    private Statement[] createParamAssignments(VariableSpecification[] specs) {
        MethodDeclaration methDecl = pm.getMethodDeclaration();
        Statement[] paramDecl = new Statement[specs.length];
        for (int i = 0; i < specs.length; i++) {
            ParameterDeclaration parDecl = methDecl.getParameterDeclarationAt(i);
            paramDecl[i] = KeYJavaASTFactory.declare(parDecl.getModifiers(),
                parDecl.getTypeReference(), specs[i]);
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
        Sort expSort = exp.getKeYJavaType(services, execContext).getSort();
        Sort typeSort = ((KeYJavaType) type).getSort();
        /* was: services.getJavaInfo().getKeYJavaType(type); */
        return expSort.extendsTrans(typeSort);
    }
}
