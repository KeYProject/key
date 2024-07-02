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

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;
import java.util.List;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/**
 * The constructor call meta construct is used to handle a allocation expression
 * like <code>new Class(...)</code>. Thereby it replaces the allocation
 * expression by a method reference to an implict method called
 * <code>&lt;init&gt;</code> that is mainly the constructor but in its
 * normalform.
 */
public class ConstructorCall extends ProgramTransformer {

    private static final String CONSTRUCTOR_CALL = "constructor-call";

    /**
     * The normal form identifier.
     */
    private static final String NORMALFORM_IDENTIFIER = //
            de.uka.ilkd.key.java.recoderext. //
                    ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER;

    // @ invariant (newObjectSV == null) != (newObjectVar == null);
    private final SchemaVariable newObjectSV;
    private final ProgramVariable newObjectVar;

    /**
     * @param name
     *            Constructor Name.
     * @param newObjectSV
     *            The {@link SchemaVariable}
     * @param consRef
     *            The constructor reference.
     */
    protected ConstructorCall(Name name, SchemaVariable newObjectSV,
            ProgramElement consRef) {
        super(name, consRef);
        this.newObjectSV = newObjectSV;
        newObjectVar = null;
    }

    /**
     * creates the metaconstruct
     *
     * @param newObjectSV
     *            TODO
     * @param consRef
     *            TODO
     */
    public ConstructorCall(SchemaVariable newObjectSV, ProgramElement consRef) {
        this(new Name(CONSTRUCTOR_CALL), newObjectSV, consRef);
    }

    /**
     * Used to programmatically produce this statement. There is no schema
     * variable instantiation, since we have a concrete variable.
     */
    public ConstructorCall(ProgramVariable pv, New n) {
        super(new Name(CONSTRUCTOR_CALL), n);
        newObjectSV = null;
        newObjectVar = pv;
    }

    /*
     * The method is optimized in the sense that instead of returning
     * <code>newObject.<init>(args);</code> a statementblock is returned which
     * evaluates the constructor's arguments and inserts a method body statement
     * rather than the method call which avoids unneccessary proof branches. As
     * <code>newObject</code> can never be <code>null</code> no null pointer
     * check is necessary.
     */
    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {

        final New constructorReference = (New) pe;
        final KeYJavaType classType = constructorReference.getTypeReference()
                .getKeYJavaType();

        if (!(classType.getJavaType() instanceof ClassDeclaration)) {
            // no implementation available
            return new ProgramElement[] { pe };
        }

        final List<Statement> stmnts = constructorCallSequence(
            constructorReference, classType, svInst, services);

        return new ProgramElement[] { KeYJavaASTFactory.block(stmnts) };
    }

    /**
     * returns a sequence of statements modelling the Java constructor call
     * semantics explicitly
     */
    protected List<Statement> constructorCallSequence(
            final New constructorReference, final KeYJavaType classType,
            SVInstantiations svInst, Services services) {
        assert (newObjectVar == null) != (newObjectSV == null);

        final ProgramVariable newObject = newObjectSV == null ? newObjectVar
                : (ProgramVariable) svInst.getInstantiation(newObjectSV);
        final ExecutionContext ec = svInst.getExecutionContext();
        final ImmutableArray<Expression> arguments = constructorReference
                .getArguments();

        final ArrayList<Statement> evaluatedArgs = new ArrayList<Statement>();

        int j = 0;
        if (services.getJavaInfo().getAttribute(
            ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, classType) != null) {
            j = 1;
        }
        final ProgramVariable[] argumentVariables = new ProgramVariable[arguments
                .size() + j];

        for (int i = 0, sz = arguments.size(); i < sz; i++) {
            argumentVariables[i] = EvaluateArgs.evaluate(arguments.get(i),
                evaluatedArgs, services, ec);
        }

        if (j == 1) {
            Sort s = services.getJavaInfo().getAttribute(
                ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, classType).sort();
            Expression enclosingThis = (Expression) (constructorReference
                    .getReferencePrefix() instanceof Expression
                            ? constructorReference.getReferencePrefix()
                            : services.getTypeConverter()
                                    .convertToProgramElement(
                                        services.getTypeConverter()
                                                .findThisForSort(s, ec)));
            argumentVariables[argumentVariables.length - 1] = EvaluateArgs
                    .evaluate(enclosingThis, evaluatedArgs, services, ec);
        }

        // get init method
        // (deliberately using classType itself as the "context type", in order
        // to allow public calls to private init methods)
        final MethodBodyStatement mbs = KeYJavaASTFactory.methodBody(
            services.getJavaInfo(), null, newObject, classType,
            NORMALFORM_IDENTIFIER, argumentVariables);

        Debug.assertTrue(mbs != null, "Call to non-existent constructor.");

        // the assignment statements + the method body statement +
        // <allocateArea> for memory areas
        final ArrayList<Statement> stmnts = new ArrayList<Statement>();

        for (int i = 0, sz = evaluatedArgs.size(); i < sz; i++) {
            stmnts.add(evaluatedArgs.get(i));
        }

        stmnts.add(mbs);

        return stmnts;
    }

}