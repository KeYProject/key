/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.pp;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.PathInExpression;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.*;
import org.key_project.rusty.ast.pat.*;
import org.key_project.rusty.ast.stmt.EmptyStatement;
import org.key_project.rusty.ast.stmt.ExpressionStatement;
import org.key_project.rusty.ast.stmt.LetStatement;
import org.key_project.rusty.ast.stmt.Statement;
import org.key_project.rusty.ast.ty.*;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.logic.op.IProgramVariable;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.rusty.rule.metaconstruct.ProgramTransformer;
import org.key_project.rusty.speclang.LoopSpecification;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.Nullable;

public class PrettyPrinter implements Visitor {
    private final PosTableLayouter layouter;

    private boolean startAlreadyMarked;
    private @Nullable Object firstStatement;
    private boolean endAlreadyMarked;

    private final SVInstantiations instantiations;
    private final @Nullable Services services;
    private boolean usePrettyPrinting;
    private boolean useUnicodeSymbols;

    /**
     * creates a new PrettyPrinter
     */
    public PrettyPrinter(PosTableLayouter out) {
        this(out, SVInstantiations.EMPTY_SVINSTANTIATIONS, null, true, true);
    }

    public PrettyPrinter(PosTableLayouter o, SVInstantiations svi, @Nullable Services services,
            boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        this.layouter = o;
        this.instantiations = svi;
        this.services = services;
        this.usePrettyPrinting = usePrettyPrinting;
        this.useUnicodeSymbols = useUnicodeSymbols;
    }

    /**
     * Creates a PrettyPrinter that does not create a position table.
     */
    public static PrettyPrinter purePrinter() {
        return new PrettyPrinter(PosTableLayouter.pure());
    }

    /**
     * @return the result
     */
    public String result() {
        return layouter.result();
    }

    /**
     * Alternative entry method for this class. Omits the trailing semicolon in the output.
     *
     * @param s source element to print
     */
    public void printFragment(RustyProgramElement s) {
        layouter.beginRelativeC(0);
        markStart(s);
        s.visit(this);
        markEnd(s);
        layouter.end();
    }

    protected void printUnaryOperator(String symbol, boolean prefix, RustyProgramElement child) {
        if (prefix) {
            layouter.print(symbol);
            child.visit(this);
        } else {
            child.visit(this);
            layouter.print(symbol);
        }
    }

    /**
     * Marks the start of the first executable statement ...
     *
     * @param stmt current statement;
     */
    protected void markStart(Object stmt) {
        if (!startAlreadyMarked) {
            layouter.markStartFirstStatement();
            firstStatement = stmt;
            startAlreadyMarked = true;
        }
    }

    /**
     * Marks the end of the first executable statement ...
     */
    protected void markEnd(Object stmt) {
        if (!endAlreadyMarked && (firstStatement == stmt)) {
            layouter.markEndFirstStatement();
            endAlreadyMarked = true;
        }
    }

    /**
     * Replace all unicode characters above ? by their explicit representation.
     *
     * @param str the input string.
     * @return the encoded string.
     */
    protected static String encodeUnicodeChars(String str) {
        int len = str.length();
        StringBuilder buf = new StringBuilder(len + 4);
        for (int i = 0; i < len; i += 1) {
            char c = str.charAt(i);
            if (c >= 0x0100) {
                if (c < 0x1000) {
                    buf.append("\\u0").append(Integer.toString(c, 16));
                } else {
                    buf.append("\\u").append(Integer.toString(c, 16));
                }
            } else {
                buf.append(c);
            }
        }
        return buf.toString();
    }

    /**
     * Write comma list.
     *
     * @param list a program element list.
     */
    protected void writeCommaList(ImmutableArray<? extends RustyProgramElement> list) {
        for (int i = 0; i < list.size(); i++) {
            if (i != 0) {
                layouter.print(",").brk();
            }
            list.get(i).visit(this);
        }
    }

    @Override
    public void performActionOnAssignmentExpression(AssignmentExpression x) {
        x.lhs().visit(this);
        layouter.print(" = ");
        x.rhs().visit(this);
    }

    private void beginBlock() {
        layouter.print("{");
        layouter.beginRelativeC();
    }

    private void endBlock() {
        layouter.end().nl().print("}");
    }

    @Override
    public void performActionOnBlockExpression(BlockExpression x) {
        if (x.getChildCount() == 0) {
            markStart(x);
            layouter.print("{}");
            markEnd(x);
        } else {
            beginBlock();
            for (Statement stmt : x.getStatements()) {
                layouter.nl();
                stmt.visit(this);
            }
            if (x.getValue() != null) {
                layouter.nl();
                x.getValue().visit(this);
            }
            endBlock();
        }
    }

    @Override
    public void performActionOnBooleanLiteralExpression(BooleanLiteralExpression x) {
        layouter.keyWord(x.getValue() ? "true" : "false");
    }

    @Override
    public void performActionOnContextBlockExpression(ContextBlockExpression x) {
        if (x.getStatements().isEmpty()) {
            layouter.print("{c# #c}");
        } else {
            layouter.beginRelativeC();
            layouter.print("{ c#");
            for (Statement stmt : x.getStatements()) {
                layouter.nl();
                stmt.visit(this);
            }
            layouter.end().nl();
            layouter.print("#c }");
        }
    }

    @Override
    public void performActionOnIntegerLiteralExpression(IntegerLiteralExpression x) {
        layouter.print(x.toString());
    }

    @Override
    public void performActionOnSchemaVariable(SchemaVariable x) {
        if (!(x instanceof ProgramSV)) {
            throw new UnsupportedOperationException(
                "Don't know how to pretty print non program SV in programs.");
        }

        Object o = instantiations.getInstantiation(x);
        if (o == null) {
            layouter.print(x.name().toString());
        } else {
            if (o instanceof RustyProgramElement pe) {
                pe.visit(this);
            } else if (o instanceof ImmutableArray) {
                for (RustyProgramElement e : ((ImmutableArray<RustyProgramElement>) o)) {
                    e.visit(this);
                }
            } else {
                // LOGGER.warn("No PrettyPrinting available for {}", o.getClass().getName());
            }
        }
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        layouter.print(x.name().toString());
    }

    @Override
    public void performActionOnEmptyStatement(EmptyStatement x) {
        layouter.print(";");
    }

    private void beginMultilineParen() {
        layouter.print("(").beginRelativeC(0).beginRelativeC().brk(0);
    }

    private void endMultilineParen() {
        layouter.end().brk(0).end();
        layouter.print(")");
    }

    private void printArguments(ImmutableArray<? extends Expr> args) {
        beginMultilineParen();
        if (args != null) {
            writeCommaList(args);
        }
        endMultilineParen();
    }

    @Override
    public void performActionOnMethodCall(MethodCallExpression x) {
        x.callee().visit(this);
        layouter.print(".");
        layouter.print(x.method().toString());
        printArguments(x.params());
    }

    @Override
    public void performActionOnFieldExpression(FieldExpression x) {
        x.base().visit(this);
        layouter.print(".");
        x.field().visit(this);
    }

    @Override
    public void performActionOnTupleIndexingExpression(TupleIndexingExpression x) {
        x.base().visit(this);
        layouter.print("." + x.index());
    }

    @Override
    public void performActionOnCallExpression(CallExpression x) {
        x.callee().visit(this);
        printArguments(x.params());
    }

    @Override
    public void performActionOnIndexExpression(IndexExpression x) {
        x.base().visit(this);
        layouter.print("[");
        x.index().visit(this);
        layouter.print("]");
    }

    @Override
    public void performActionOnErrorPropagationExpression(ErrorPropagationExpression x) {
        printUnaryOperator("?", false, x.expr());
    }

    @Override
    public void performActionOnBorrowExpression(BorrowExpression x) {
        layouter.print("&");
        if (x.isMut()) {
            layouter.keyWord("mut");
            layouter.print(" ");
        }
        x.getExpr().visit(this);
    }

    @Override
    public void performActionOnDereferenceExpression(DereferenceExpression x) {
        printUnaryOperator("*", true, x.expr());
    }

    @Override
    public void performActionOnTypeCastExpression(TypeCastExpression x) {
        x.expr().visit(this);
        layouter.print(" ");
        layouter.keyWord("as");
        layouter.brk();
        // TODO: type
    }

    @Override
    public void performActionOnRangeExpression(RangeExpression x) {
        if (x.left() != null) {
            x.left().visit(this);
        }
        layouter.print(x.inclusive() ? "..=" : "..");
        if (x.right() != null) {
            x.right().visit(this);
        }
    }

    @Override
    public void performActionOnCompoundAssignmentExpression(CompoundAssignmentExpression x) {
        x.left().visit(this);
        layouter.print(" ");
        x.op().visit(this);
        layouter.print("= ");
        x.right().visit(this);
    }

    @Override
    public void performActionOnContinueExpression(ContinueExpression x) {
        layouter.keyWord("continue");
        if (x.expr() != null) {
            layouter.brk();
            x.expr().visit(this);
        }
    }

    @Override
    public void performActionOnBreakExpression(BreakExpression x) {
        layouter.keyWord("break");
        if (x.expr() != null) {
            layouter.brk();
            x.expr().visit(this);
        }
    }

    @Override
    public void performActionOnReturnExpression(ReturnExpression x) {
        layouter.keyWord("return");
        if (x.expr() != null) {
            layouter.brk();
            x.expr().visit(this);
        }
    }

    @Override
    public void performActionOnGroupedExpression(GroupedExpression x) {
        layouter.print("(");
        x.expr().visit(this);
        layouter.print(")");
    }

    @Override
    public void performActionOnEnumeratedArrayExpression(EnumeratedArrayExpression x) {

    }

    @Override
    public void performActionOnRepeatedArrayExpression(RepeatedArrayExpression x) {
        layouter.print("[");
        x.expr().visit(this);
        layouter.print("; ");
        x.size().visit(this);
        layouter.print("]");
    }

    @Override
    public void performActionOnTupleExpression(TupleExpression x) {
        layouter.print("(");
        writeCommaList(x.elements());
        layouter.print(")");
    }

    @Override
    public void performActionOnPathInExpression(PathInExpression x) {
        var segments = x.segments();
        for (int i = 0; i < segments.size(); i++) {
            if (i != 0) {
                layouter.print("::");
            }
            layouter.print(segments.get(i).toString());
        }
    }

    @Override
    public void performActionOnTupleStructExpression(TupleStructExpression x) {

    }

    @Override
    public void performActionOnUnitStructExpression(UnitStructExpression x) {

    }

    @Override
    public void performActionOnFieldStructExpression(StructStructExpression x) {

    }

    @Override
    public void performActionOnEnumVariantFieldless(EnumVariantFieldless x) {

    }

    @Override
    public void performActionOnEnumVariantTuple(EnumVariantTuple x) {

    }

    @Override
    public void performActionOnClosureExpression(ClosureExpression x) {

    }

    @Override
    public void performActionOnEnumVariantStruct(EnumVariantStruct x) {

    }

    @Override
    public void performActionOnInfiniteLoop(InfiniteLoopExpression x) {
        layouter.keyWord("loop").print(" ");
        x.body().visit(this);
    }

    @Override
    public void performActionOnPredicatePatternLoopExpression(PredicatePatternLoopExpression x) {
        layouter.print("while").print(" ");
        x.expr().visit(this);
        layouter.print(" ");
        x.body().visit(this);
    }

    @Override
    public void performActionOnIteratorLoopExpression(IteratorLoopExpression x) {
        layouter.keyWord("for").print(" ");
        x.pattern().visit(this);
        layouter.print(" ");
        layouter.keyWord("in");
        layouter.print(" ");
        x.expr().visit(this);
        layouter.print(" ");
        x.body().visit(this);
    }

    @Override
    public void performActionOnIfExpression(IfExpression x) {
        layouter.keyWord("if").print(" ");
        x.condition().visit(this);
        layouter.print(" ");
        x.thenExpr().visit(this);
        if (x.elseExpr() != null) {
            layouter.print(" ");
            layouter.keyWord("else").print(" ");
            x.elseExpr().visit(this);
        }
    }

    @Override
    public void performActionOnMatchExpression(MatchExpression x) {

    }

    @Override
    public void performActionOnMatchArm(MatchArm x) {

    }

    @Override
    public void performActionOnExpressionStatement(ExpressionStatement x) {
        x.getExpression().visit(this);
        layouter.print(";");
    }

    @Override
    public void performActionOnPrimitiveRustType(PrimitiveRustType x) {
        layouter.print(x.type().toString());
    }

    @Override
    public void performActionOnSchemaRustType(SchemaRustType x) {
        layouter.print("s#" + x.type().toString());
    }

    @Override
    public void performActionOnLetStatement(LetStatement x) {
        layouter.keyWord("let").print(" ");
        x.getPattern().visit(this);
        layouter.print(": ");
        x.type().visit(this);
        if (x.hasInit()) {
            layouter.print(" = ");
            x.getInit().visit(this);
        }
        layouter.print(";");
    }

    @Override
    public void performActionOnIdentPattern(IdentPattern x) {
        if (x.isReference()) {
            layouter.keyWord("ref");
            layouter.print(" ");
        }
        if (x.isMutable()) {
            layouter.keyWord("mut");
            layouter.print(" ");
        }
        layouter.print(x.name().toString());
    }

    @Override
    public void performActionOnSchemaVarPattern(SchemaVarPattern x) {

    }

    @Override
    public void performActionOnLiteralPattern(LiteralPattern x) {

    }

    @Override
    public void performActionOnAltPattern(AltPattern x) {

    }

    @Override
    public void performActionOnWildCardPattern(WildCardPattern x) {

    }

    @Override
    public void performActionOnRangepattern(RangePattern x) {
        if (x.left() != null) {
            x.left().visit(this);
        }
        layouter.print(x.bounds().toString());
        if (x.right() != null) {
            x.right().visit(this);
        }
    }

    @Override
    public void performActionOnReferenceRustType(ReferenceRustType x) {
        layouter.print("&");
        if (x.isMut()) {
            layouter.keyWord("mut");
            layouter.print(" ");
        }
        x.inner().visit(this);
    }

    @Override
    public void performActionOnBinaryExpression(BinaryExpression x) {
        x.left().visit(this);
        layouter.print(" ");
        x.op().visit(this);
        layouter.print(" ");
        x.right().visit(this);
    }

    @Override
    public void performActionOnBinaryOperator(BinaryExpression.Operator x) {
        layouter.print(x.toString());
    }

    @Override
    public void performActionOnUnaryExpression(UnaryExpression x) {
        x.op().visit(this);
        x.expr().visit(this);
    }

    @Override
    public void performActionOnUnaryOperator(UnaryExpression.Operator x) {
        layouter.print(x.toString());
    }

    @Override
    public void performActionOnBindingPattern(BindingPattern x) {
        if (x.ref()) {
            layouter.keyWord("ref");
            layouter.print(" ");
        }
        x.pv().visit(this);
        if (x.opt() != null) {
            layouter.print(" @ ");
            x.opt().visit(this);
        }
    }

    @Override
    public void performActionOnLetExpression(LetExpression x) {
        layouter.keyWord("let");
        layouter.print(" ");
        x.pat().visit(this);
        if (x.ty() != null) {
            layouter.print(": ");
            x.ty().visit(this);
        }
        layouter.print(" = ");
        x.init().visit(this);
    }

    @Override
    public void performActionOnTypeOf(TypeOf x) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void performActionOnProgramFunction(ProgramFunction x) {

    }

    @Override
    public void performActionOnFunctionBodyExpression(FunctionBodyExpression x) {
        var result = x.resultVar();
        if (result != null) {
            result.visit(this);
            layouter.brk(1, 0);
            layouter.print("=");
            layouter.brk(1, 0);
        }
        x.call().visit(this);
        layouter.print("@");
    }

    @Override
    public void performActionOnFunctionFrame(FunctionFrame x) {
        layouter.keyWord("fn-frame");
        layouter.print(" ");
        beginMultilineParen();

        IProgramVariable var = x.getResultVar();
        var fn = x.getFunction();
        if (var != null) {
            layouter.beginRelativeC().print("result->");
            var.visit(this);
            if (fn != null) {
                layouter.print(",");
            }
            layouter.end();
            if (fn != null) {
                layouter.brk();
            }
        }

        if (fn != null) {
            layouter.print(fn.getFunction().name().toString());
        }

        endMultilineParen();
        layouter.print(" ");

        if (x.getBody() != null) {
            x.getBody().visit(this);
        }
    }

    @Override
    public void performActionOnLoopInvariant(LoopSpecification x) {

    }

    @Override
    public void performActionOnProgramMetaConstruct(ProgramTransformer x) {
        layouter.print(x.name().toString());
        layouter.print("(");
        if (x.getChildCount() > 0)
            ((RustyProgramElement) x.getChild(0)).visit(this);
        layouter.print(")");
    }

    @Override
    public void performActionOnLoopScope(LoopScope x) {
        layouter.keyWord("loop_scope!");
        beginMultilineParen();
        if (x.getIndex() != null) {
            x.getIndex().visit(this);
            layouter.print(", ");
        }

        x.getBlock().visit(this);
        endMultilineParen();
    }

    @Override
    public void performActionOnSortRustType(SortRustType x) {
        layouter.print(x.getSort(services).name().toString());
    }

    @Override
    public void performActionOnLitPatExpr(LitPatExpr x) {
        if (x.isNegated()) {
            layouter.print("-");
        }
        x.getLit().visit(this);
    }
}
