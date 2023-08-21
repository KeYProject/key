/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.IntersectionType;
import recoder.abstraction.Method;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.convenience.TreeWalker;
import recoder.java.Expression;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.expression.operator.Conditional;
import recoder.java.reference.MethodReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;

/**
 * Deals with uses of the conditional(c-like trinary) operator which create intersection types.
 *
 * @author Tobias Gutzmann
 */
// * Conditionals which have conditionals in their subtree (i.e. (part of their) operands)
// * are not being considered. analyze() will report INCOMPLETE in such a case.
// * For complete effect, run again (and again(and again...)).
public class MakeConditionalCompatible extends TwoPassTransformation {

    private final NonTerminalProgramElement root;
    private List<Item> list;

    /**
     * @param sc
     */
    public MakeConditionalCompatible(CrossReferenceServiceConfiguration sc,
            NonTerminalProgramElement root) {
        super(sc);
        this.root = root;
    }

    @Override
    public ProblemReport analyze() {
        list = new ArrayList<>();
        setProblemReport(NO_PROBLEM);
        TreeWalker tw = new TreeWalker(root);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof Conditional) {
                Conditional c = (Conditional) pe;
                Type t = getSourceInfo().getType(c);
                Type e1 = getSourceInfo().getType(c.getExpressionAt(1));
                Type e2 = getSourceInfo().getType(c.getExpressionAt(2));
                if (t instanceof IntersectionType || (e1 != e2
                        && !(e1 instanceof PrimitiveType && e2 instanceof PrimitiveType)
                        && !(e1 == getNameInfo().getNullType())
                        && !(e2 == getNameInfo().getNullType())
                        && !getSourceInfo().isWidening(e1, e2)
                        && !getSourceInfo().isWidening(e2, e1))) {
                    Expression parent = (Expression) c.getASTParent();
                    Type target;
                    if (parent instanceof MethodReference) {
                        Method m = getSourceInfo().getMethod((MethodReference) parent);
                        target = m.getContainingClassType();
                    } else {
                        target = getSourceInfo().getType(parent);
                    }
                    // TODO any other special cases?
                    list.add(new Item(c, target));
                }
            }
        }
        if (list.isEmpty()) {
            return IDENTITY;
        }
        return NO_PROBLEM;
    }

    @Override
    public void transform() {
        super.transform();
        ProgramFactory f = getProgramFactory();
        for (Item i : list) {
            Expression e1 = i.c.getExpressionAt(1);
            Expression e2 = i.c.getExpressionAt(2);
            replace(e1, f.createTypeCast(e1.deepClone(), TypeKit.createTypeReference(f, i.t)));
            replace(e2, f.createTypeCast(e2.deepClone(), TypeKit.createTypeReference(f, i.t)));
        }
    }

    private static class Item {
        final Conditional c;
        final Type t;

        Item(Conditional c, Type t) {
            this.c = c;
            this.t = t;
        }
    }


}
