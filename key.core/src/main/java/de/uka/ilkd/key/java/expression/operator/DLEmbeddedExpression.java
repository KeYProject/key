/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.logic.sort.Sort;
import org.key_project.util.ExtList;

public class DLEmbeddedExpression extends Operator {

    private final JFunction functionSymbol;

    /**
     * @return the functionSymbol
     */
    public JFunction getFunctionSymbol() {
        return functionSymbol;
    }

    public DLEmbeddedExpression(JFunction f, ExtList children) {
        super(children);
        this.functionSymbol = f;
    }

    /**
     * Arity of an embedded JavaDL Expression depends upon the number of arguments.
     *
     * Since the first argument may be implicitly given, we cannot use the arity of
     * {@link #functionSymbol}.
     */
    @Override
    public int getArity() {
        // return functionSymbol.arity();
        return children.size();
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.java.expression.Operator#getKeYJavaType(de.uka.ilkd.key.java.Services,
     * de.uka.ilkd.key.java.reference.ExecutionContext)
     */
    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {

        Sort sort = functionSymbol.sort();

        KeYJavaType kjt = getKeYJavaType(javaServ, sort);
        if (kjt != null) {
            return kjt;
        } else {
            // FIXME FIXME FIXME Unknown types are mapped to int.
            return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
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

        String name = containingClass.getSort().name().toString();
        String qualifier =
            name.lastIndexOf('.') != -1 ? name.substring(0, name.lastIndexOf('.')) : "";
        name = name.substring(name.lastIndexOf('.') + 1);
        TypeRef tr = new TypeRef(new ProgramElementName(name, qualifier), 0, null, containingClass);
        ExecutionContext ec = new ExecutionContext(tr, null, null);

        for (int i = 0; i < actual; i++) {
            Sort argSort = functionSymbol.argSort(i + implicitOffset);
            KeYJavaType kjtExpected = getKeYJavaType(javaServ, argSort);

            Expression child = children.get(i);


            KeYJavaType kjtActual = javaServ.getTypeConverter().getKeYJavaType(child, ec);

            if (kjtExpected != null && !kjtActual.getSort().extendsTrans(kjtExpected.getSort())) {
                throw new ConvertException(
                    "Received " + child + " as argument " + i + " for function " + functionSymbol
                        + ". Was expecting type " + kjtExpected + ", but received " + kjtActual);
            }
        }
    }


    private static Sort getHeapSort(Services javaServ) {
        return javaServ.getTypeConverter().getHeapLDT().targetSort();
    }

    private static KeYJavaType getKeYJavaType(Services javaServ, Sort argSort) {
        // JavaInfo returns wrong data for sort integer! We need to find it over
        // other paths.
        JavaInfo javaInfo = javaServ.getJavaInfo();
        KeYJavaType intType = javaInfo.getPrimitiveKeYJavaType("int");
        if (argSort == intType.getSort()) {
            return intType;
        } else {
            return javaInfo.getKeYJavaType(argSort);
        }
    }

    public Term makeTerm(LocationVariable heap, Term[] subs, Services services) {
        JFunction f = getFunctionSymbol();
        // we silently assume that check has been called earlier

        if (f.arity() == subs.length) {
            return services.getTermFactory().createTerm(f, subs);
        } else {
            Term[] extSubs = new Term[subs.length + 1];
            System.arraycopy(subs, 0, extSubs, 1, subs.length);
            extSubs[0] = services.getTermBuilder().var(heap);
            return services.getTermFactory().createTerm(f, extSubs);
        }
    }
}
