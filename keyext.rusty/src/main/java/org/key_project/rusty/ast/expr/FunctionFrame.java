/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.ProgramPrefixUtil;
import org.key_project.rusty.ast.abstraction.TupleType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.logic.PosInProgram;
import org.key_project.rusty.logic.PossibleProgramPrefix;
import org.key_project.rusty.logic.op.IProgramVariable;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.Nullable;

public class FunctionFrame implements Expr, PossibleProgramPrefix {
    private final @Nullable IProgramVariable resultVar;
    private final BlockExpression body;

    private final PosInProgram firstActiveChildPos;
    private final int prefixLength;
    private final @Nullable FunctionFrame innermostFunctionFrame;

    private final ProgramFunction function;

    public FunctionFrame(@Nullable IProgramVariable resultVar, ProgramFunction function,
            BlockExpression body) {
        this.resultVar = resultVar;
        this.body = body;

        firstActiveChildPos = body.getChildCount() == 0 ? PosInProgram.TOP
                : PosInProgram.TOP.down(getChildCount() - 1).down(0);

        var info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.length();
        innermostFunctionFrame = info.innermostFunctionFrame();
        this.function = function;
    }

    public FunctionFrame(ExtList children) {
        resultVar = children.get(IProgramVariable.class);
        function = children.get(ProgramFunction.class);
        body = children.get(BlockExpression.class);

        firstActiveChildPos = body.getChildCount() == 0 ? PosInProgram.TOP
                : PosInProgram.TOP.down(getChildCount() - 1).down(0);

        var info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.length();
        innermostFunctionFrame = info.innermostFunctionFrame();
    }

    public @Nullable IProgramVariable getResultVar() {
        return resultVar;
    }

    public BlockExpression getBody() {
        return body;
    }

    @Override
    public boolean isPrefix() {
        return body.getChildCount() != 0;
    }

    @Override
    public boolean hasNextPrefixElement() {
        return body.getChildCount() != 0 && body.getChild(0) instanceof PossibleProgramPrefix;
    }

    @Override
    public PossibleProgramPrefix getNextPrefixElement() {
        if (hasNextPrefixElement())
            return (PossibleProgramPrefix) body.getChild(0);
        throw new IndexOutOfBoundsException("No next prefix element " + this);
    }

    @Override
    public PossibleProgramPrefix getLastPrefixElement() {
        return hasNextPrefixElement() ? getNextPrefixElement().getLastPrefixElement() : this;
    }

    @Override
    public int getPrefixLength() {
        return prefixLength;
    }

    public @Nullable FunctionFrame getInnermostFunctionFrame() {
        return innermostFunctionFrame;
    }

    @Override
    public ImmutableArray<PossibleProgramPrefix> getPrefixElements() {
        return BlockExpression.computePrefixElements(body);
    }

    @Override
    public PosInProgram getFirstActiveChildPos() {
        return firstActiveChildPos;
    }

    @Override
    public Type type(Services services) {
        return TupleType.UNIT;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnFunctionFrame(this);
    }

    @Override
    public SyntaxElement getChild(int n) {
        if (resultVar != null) {
            if (n == 0)
                return resultVar;
            --n;
        }
        if (body != null) {
            if (n == 0)
                return body;
            --n;
        }
        throw new IndexOutOfBoundsException("No next child");
    }

    @Override
    public int getChildCount() {
        int result = 0;
        if (resultVar != null)
            result += 1;
        if (body != null)
            result += 1;
        return result;
    }

    public ProgramFunction getFunction() {
        return function;
    }

    @Override
    public String toString() {
        return "fn_frame!(result->" + resultVar + ", " + (function == null ? null : function.name())
            + ")" + body;
    }
}
