/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.HashMap;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.ReferencePrefix;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.ast.statement.LoopStatement;
import de.uka.ilkd.key.java.ast.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableList;

/**
 * Replaces the MethodBodyStatement shortcut with the full body, performs prefix adjustments in the
 * body (execution context).
 */
@TransformerMeta(name = "#expandMethodBody")
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
        ImmutableList<? extends Expression> argsAsParam = mbs.getArguments();

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
        result = (StatementBlock) paramRepl.result();

        // Keep the parameter-renamed loop specifications reachable from the source loops. A
        // later taclet application may rebuild a loop from its textual pattern, which does not
        // carry the node-attached specification.
        var sourceLoops = new JavaASTCollector(methDecl.getBody(), LoopStatement.class);
        sourceLoops.start();
        var expandedLoops = new JavaASTCollector(result, LoopStatement.class);
        expandedLoops.start();
        var sourceNodes = sourceLoops.getNodes();
        var expandedNodes = expandedLoops.getNodes();
        for (int i = 0; i < Math.min(sourceNodes.size(), expandedNodes.size()); i++) {
            var expanded = (LoopStatement) expandedNodes.get(i);
            if (expanded.getLoopInvariant() != null) {
                ((LoopStatement) sourceNodes.get(i)).setExpandedLoopInvariant(
                    expanded.getLoopInvariant());
            }
        }

        return new ProgramElement[] { KeYJavaASTFactory.methodFrame(mbs.getResultVariable(),
            KeYJavaASTFactory.executionContext(mbs.getBodySource(), pm, newCalled), result,
            PositionInfo.UNDEFINED) };
    }


    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of(body());
    }
}
