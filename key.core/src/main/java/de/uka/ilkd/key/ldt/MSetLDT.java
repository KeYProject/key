/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.expression.literal.*;
import de.uka.ilkd.key.java.ast.expression.operator.mst.*;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;

import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableList;

public class MSetLDT extends LDT {

    public static final Name NAME = new Name("Mset");

    private final ParametricFunctionDecl msetRange;
    private final ParametricFunctionDecl msetEmpty;
    private final ParametricFunctionDecl msetSingle;
    private final ParametricFunctionDecl msetSum;
    private final ParametricFunctionDecl msetDiff;
    private final Function msetCard;
    private final Function msetMul;

    public MSetLDT(TermServices services) {
        super(NAME, services);
        msetMul = addFunction(services, "msetMul");
        msetEmpty = addParametricFunction(services, "msetEmpty");
        msetSingle = addParametricFunction(services, "msetSingle");
        msetSum = addParametricFunction(services, "msetSum");
        msetDiff = addParametricFunction(services, "msetDiff");
        msetCard = addFunction(services, "msetCard");
        msetRange = addParametricFunction(services, "msetRange");
    }


    public ParametricFunctionDecl getMsetRange() { return msetRange; }

    /**
     * Returns the select function for the given sort.
     */
    public ParametricFunctionInstance getMsetRange(Sort instanceSort, TermServices services) {
        return ParametricFunctionInstance.get(msetRange,
                ImmutableList.of(new GenericArgument(instanceSort)), (Services) services);
    }


    public Function getMsetMul() {
        return msetMul;
    }

    public ParametricFunctionDecl getMsetEmpty() {
        return msetEmpty;
    }

    /**
     * Returns the select function for the given sort.
     */
    public ParametricFunctionInstance getMsetEmpty(Sort instanceSort, TermServices services) {
        return ParametricFunctionInstance.get(msetEmpty,
                ImmutableList.of(new GenericArgument(instanceSort)), (Services) services);
    }


    public ParametricFunctionDecl getMsetSingle() {
        return msetSingle;
    }

    /**
     * Returns the select function for the given sort.
     */
    public ParametricFunctionInstance getMsetSingle(Sort instanceSort, TermServices services) {
        return ParametricFunctionInstance.get(msetSingle,
                ImmutableList.of(new GenericArgument(instanceSort)), (Services) services);
    }

    public ParametricFunctionDecl getMsetSum() {
        return msetSum;
    }

    /**
     * Returns the select function for the given sort.
     */
    public ParametricFunctionInstance getMsetSum(Sort instanceSort, TermServices services) {
        return ParametricFunctionInstance.get(msetSum,
                ImmutableList.of(new GenericArgument(instanceSort)), (Services) services);
    }



    public ParametricFunctionDecl getMsetDiff() {
        return msetDiff;
    }

    /**
     * Returns the select function for the given sort.
     */
    public ParametricFunctionInstance getMsetDiff(Sort instanceSort, TermServices services) {
        return ParametricFunctionInstance.get(msetDiff,
                ImmutableList.of(new GenericArgument(instanceSort)), (Services) services);
    }

    @Override
    public boolean isResponsible(Operator op, JTerm[] subs, Services services,
            ExecutionContext ec) {
        return op instanceof MSetCard || op instanceof MSetMul
                || op instanceof de.uka.ilkd.key.java.ast.expression.operator.mst.MSetSingle
                || op instanceof MSetIntersect ||
                op instanceof MSetDiff || op instanceof MSetUnion || op instanceof MSetSum;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm left, JTerm right, Services services,
            ExecutionContext ec) {
        return op instanceof MSetUnion || op instanceof MSetIntersect
                || op instanceof de.uka.ilkd.key.java.ast.expression.operator.mst.MSetSum
                || op instanceof MSetDiff;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm sub, TermServices services,
            ExecutionContext ec) {
        return op instanceof MSetSingle || op instanceof MSetMul || op instanceof MSetCard;
    }

    @Override
    public JTerm translateLiteral(Literal lit, Services services) {
        throw new RuntimeException("Not implemented yet");
//        assert lit instanceof EmptyMSetLiteral;
//        return services.getTermBuilder().func(msetEmpty, lit.g);
    }

    @Override
    public Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        throw new RuntimeException("Not implemented yet");
        //        if (op instanceof MSetSingle) {
//            return msetSingle;
//        } else if (op instanceof MSetCard) {
//            return msetCard;
//        } else if (op instanceof MSetUnion) {
//            return msetUnion;
//        } else if (op instanceof MSetDiff) {
//            return msetDiff;
//        } else if (op instanceof MSetSum) {
//            return msetSum;
//        } else if (op instanceof MSetIntersect) {
//            return msetIntersec;
//        } else if (op instanceof MSetMul) {
//            return msetMul;
//        }
//
//        assert false;
//        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return f.equals(msetEmpty);
    }

    @Override
    public Expression translateTerm(JTerm t, ExtList children, Services services) {
        if (t.op().equals(msetEmpty)) {
            return EmptyMSetLiteral.INSTANCE;
        }
        assert false;
        return null;
    }

    @Override
    public Type getType(JTerm t) {
        assert false;
        return null;
    }
}
