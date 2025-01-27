/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.metaconstruct;

import java.util.HashMap;

import org.key_project.logic.Name;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.expr.FunctionBodyExpression;
import org.key_project.rusty.ast.expr.FunctionFrame;
import org.key_project.rusty.ast.visitor.ProgVarReplaceVisitor;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.rule.inst.SVInstantiations;

public class ExpandFnBody extends ProgramTransformer {
    public ExpandFnBody(ProgramSV programSV) {
        super(new Name("expand_fn_body"), programSV);
    }

    @Override
    public RustyProgramElement[] transform(RustyProgramElement pe, Services services,
            SVInstantiations svInst) {
        var fb = (FunctionBodyExpression) pe;
        var fn = fb.fn();

        BlockExpression result = fb.getBody();

        final HashMap<ProgramVariable, ProgramVariable> map = new HashMap<>();
        final var params = fn.collectParameters();

        for (int i = 0; i < params.size(); i++) {
            var param = (ProgramVariable) fb.call().params().get(i);
            var pv = params.get(i);
            map.put(pv, param);
        }

        var paramRepl = new ProgVarReplaceVisitor(result, map, true, services);
        paramRepl.start();
        result = (BlockExpression) paramRepl.result();

        return new RustyProgramElement[] {
            new FunctionFrame(fb.resultVar(), fn, result)
        };
    }
}
