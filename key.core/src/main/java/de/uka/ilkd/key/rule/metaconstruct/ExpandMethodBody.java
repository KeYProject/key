/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.HashMap;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.util.collection.ImmutableArray;

/**
 * Replaces the MethodBodyStatement shortcut with the full body, performs prefix adjustments in the
 * body (execution context).
 */
public class ExpandMethodBody extends ProgramTransformer {

    public ExpandMethodBody(SchemaVariable sv) {
        super(new Name("expand-method-body"), (ProgramSV) sv);
    }

    public ExpandMethodBody(Statement mb) {
        super(new Name("expand-method-body"), mb);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {

        MethodBodyStatement mbs = (MethodBodyStatement) pe;
        // MethodReference mr = mbs.getMethodReference();

        IProgramMethod pm = mbs.getProgramMethod(services);
        // mr.method(services, mbs.getBodySource());

        MethodDeclaration methDecl = pm.getMethodDeclaration();

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

        final HashMap<ProgramVariable, ProgramVariable> map = new LinkedHashMap<>();
        for (int i = 0; i < argsAsParam.size(); i++) {
            IProgramVariable pv = methDecl.getParameterDeclarationAt(i).getVariableSpecification()
                    .getProgramVariable();
            assert pv instanceof ProgramVariable : "Unexpected schematic variable";
            Expression arg = argsAsParam.get(i);
            assert arg instanceof ProgramVariable : "Unexpected schematic variable";
            map.put((ProgramVariable) pv, (ProgramVariable) argsAsParam.get(i));
        }
        ProgVarReplaceVisitor paramRepl = new ProgVarReplaceVisitor(result, map, services);
        paramRepl.start();
        result = (StatementBlock) paramRepl.result();

        return new ProgramElement[] { KeYJavaASTFactory.methodFrame(mbs.getResultVariable(),
            KeYJavaASTFactory.executionContext(mbs.getBodySource(), pm, newCalled), result,
            PositionInfo.UNDEFINED) };
    }

}
