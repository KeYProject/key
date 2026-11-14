/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Objects;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.ReferencePrefix;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.ast.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;

/**
 * Replaces the MethodBodyStatement shortcut with the full body, performs prefix adjustments in the
 * body (execution context).
 */
@TransformerMeta(name = "#expandMethodBody")
@NullMarked
public class ExpandMethodBody extends ProgramTransformer {

    public ExpandMethodBody(SchemaVariable sv) {
        super(new Name("#expandMethodBody"), (ProgramSV) sv);
    }

    public ExpandMethodBody(Statement mb) {
        super(new Name("#expandMethodBody"), mb);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {

        MethodBodyStatement mbs = (MethodBodyStatement) pe;
        // MethodReference mr = mbs.getMethodReference();

        IProgramMethod pm = mbs.getProgramMethod(services);
        // mr.method(services, mbs.getBodySource());

        MethodDeclaration methDecl = Objects.requireNonNull(pm.getMethodDeclaration(),
            "no method declaration for " + pm);

        StatementBlock result = (StatementBlock) mbs.getBody(services);
        ReferencePrefix newCalled = mbs.getDesignatedContext();
        if (newCalled instanceof TypeReference) {
            // static method
            newCalled = null;
        }

        // removed this again. see bugs #437,#479 -- vladimir
        // result = prettyNewObjectNames(result, methDecl, classContext);

        // at this point all arguments should be program variables
        ImmutableArray<? extends Expression> argsAsParam = mbs.getArguments();

        final HashMap<LocationVariable, LocationVariable> map = new LinkedHashMap<>();
        for (int i = 0; i < argsAsParam.size(); i++) {
            IProgramVariable pv = methDecl.getParameterDeclarationAt(i).getVariableSpecification()
                    .getProgramVariable();
            assert pv instanceof ProgramVariable : "Unexpected schematic variable";
            Expression arg = argsAsParam.get(i);
            assert arg instanceof ProgramVariable : "Unexpected schematic variable";
            map.put((LocationVariable) pv, (LocationVariable) argsAsParam.get(i));
        }
        ProgVarReplaceVisitor paramRepl = new ProgVarReplaceVisitor(result, map, services);
        paramRepl.start();
        result = (StatementBlock) Objects.requireNonNull(paramRepl.result(),
            "no expanded method body");

        return new ProgramElement[] { KeYJavaASTFactory.methodFrame(mbs.getResultVariable(),
            new ExecutionContext(new TypeRef(mbs.getBodySource()), pm, newCalled), result,
            PositionInfo.UNDEFINED) };
    }


    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of(body());
    }
}
