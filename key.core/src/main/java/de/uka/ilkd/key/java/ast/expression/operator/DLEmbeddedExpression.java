/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.expression.operator;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.logic.sort.Sort;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class DLEmbeddedExpression extends Operator {
    private final JFunction functionSymbol;

    public DLEmbeddedExpression(
            PositionInfo pi, List<Comment> comments, JFunction functionSymbol,
            ImmutableArray<Expression> children) {
        super(pi, comments, children);
        this.functionSymbol = functionSymbol;
    }

    public DLEmbeddedExpression(JFunction f, ExtList children) {
        super(children);
        this.functionSymbol = f;
    }

    public JFunction getFunctionSymbol() {
        return functionSymbol;
    }

    /**
     * Arity of an embedded JavaDL Expression depends upon the number of arguments.
     * <p>
     * Since the first argument may be implicitly given, we cannot use the arity of
     * {@link #functionSymbol}.
     */
    @Override
    public int getArity() {
        return children.size();
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.java.expression.Operator#getKeYJavaType(de.uka.ilkd.key.java.Services,
     * de.uka.ilkd.key.java.reference.ExecutionContext)
     */
    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, @Nullable ExecutionContext ec) {

        Sort sort = functionSymbol.sort();

        KeYJavaType kjt = getKeYJavaType(javaServ, sort);
        if (kjt != null) {
            return kjt;
        } else {
            // FIXME FIXME FIXME Unknown types are mapped to int.
            return Objects.requireNonNull(
                javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT),
                "no KeYJavaType for \\int");
        }
    }

    @Override
    public int getNotation() {
        return PREFIX;
    }

    @Override
    public int getPrecedence() {
        return 0;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnDLEmbeddedExpression(this);
    }

    public void check(Services javaServ, KeYJavaType containingClass) throws ConvertException {

        if (functionSymbol == null) {
            throw new ConvertException("null function symbol");
        }

        int expected = functionSymbol.arity();
        int actual = children.size();
        // if the first argument is the implicit heap argument, then shift everything
        // by one
        int implicitOffset = 0;

        if (actual == expected - 1 && functionSymbol.argSort(0) == getHeapSort(javaServ)) {
            implicitOffset = 1;
        }

        if (expected != actual + implicitOffset) {
            throw new ConvertException("Function symbol " + functionSymbol + " requires " + expected
                + " arguments, but received only " + actual);
        }

        final Sort containingSort = Objects.requireNonNull(containingClass.getSort(),
            "no sort for containing class " + containingClass);
        String name = containingSort.name().toString();
        String qualifier =
            name.lastIndexOf('.') != -1 ? name.substring(0, name.lastIndexOf('.')) : "";
        name = name.substring(name.lastIndexOf('.') + 1);
        final ProgramElementName programName =
            qualifier.isEmpty() ? new ProgramElementName(name)
                    : new ProgramElementName(name, qualifier);
        TypeRef tr = new TypeRef(programName, 0, null, containingClass);
        ExecutionContext ec = new ExecutionContext(tr, null, null);

        for (int i = 0; i < actual; i++) {
            Sort argSort = functionSymbol.argSort(i + implicitOffset);
            KeYJavaType kjtExpected = getKeYJavaType(javaServ, argSort);

            Expression child = children.get(i);


            KeYJavaType kjtActual = javaServ.getTypeConverter().getKeYJavaType(child, ec);

            if (kjtExpected != null && !Objects.requireNonNull(kjtActual.getSort(),
                "no sort for actual type " + kjtActual).extendsTrans(
                    Objects.requireNonNull(
                        kjtExpected.getSort(), "no sort for expected type " + kjtExpected))) {
                throw new ConvertException(
                    "Received " + child + " as argument " + i + " for function " + functionSymbol
                        + ". Was expecting type " + kjtExpected + ", but received " + kjtActual);
            }
        }
    }


    private static Sort getHeapSort(Services javaServ) {
        return Objects.requireNonNull(javaServ.getTypeConverter().getHeapLDT(),
            "heap theory not initialized").targetSort();
    }

    private static @Nullable KeYJavaType getKeYJavaType(Services javaServ, Sort argSort) {
        // JavaInfo returns wrong data for sort integer! We need to find it over
        // other paths.
        JavaInfo javaInfo = javaServ.getJavaInfo();
        final KeYJavaType intType = Objects.requireNonNull(
            javaInfo.getPrimitiveKeYJavaType("int"), "no KeYJavaType for primitive type \"int\"");
        if (argSort == intType.getSort()) {
            return intType;
        } else {
            return javaInfo.getKeYJavaType(argSort);
        }
    }

    public JTerm makeTerm(LocationVariable heap, JTerm[] subs, Services services) {
        // we silently assume that check has been called earlier
        if (functionSymbol.arity() == subs.length) {
            return services.getTermFactory().createTerm(functionSymbol, subs);
        } else {
            JTerm[] extSubs = new JTerm[subs.length + 1];
            System.arraycopy(subs, 0, extSubs, 1, subs.length);
            extSubs[0] = services.getTermBuilder().var(heap);
            return services.getTermFactory().createTerm(functionSymbol, extSubs);
        }
    }
}
