/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ArrayLengthReference;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.PrettyPrinter;

import org.key_project.util.ExtList;

/**
 * Replaces field references o.a by methodcalls o._a(). This is needed for unit test generation.
 */
public class FieldReplaceVisitor extends CreatingASTVisitor {

    private ProgramElement result = null;

    // private KeYJavaType containingKJT=null

    public FieldReplaceVisitor(final ProgramElement pe, final Services services) {
        super(pe, true, services);
    }

    /** starts the walker */
    @Override
    public void start() {
        stack.push(new ExtList());
        walk(root());
        final ExtList el = stack.peek();
        int i = 0;
        while (!(el.get(i) instanceof ProgramElement)) {
            i++;
        }
        result = (ProgramElement) stack.peek().get(i);
    }

    public ProgramElement result() {
        return result;
    }

    @Override
    public void performActionOnFieldReference(final FieldReference x) {
        final ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
        }
        changeList.removeFirstOccurrence(PositionInfo.class);
        if (x.getReferencePrefix() != null) {
            final Expression field = (Expression) changeList.get(1);
            if (field instanceof ProgramVariable) {
                final String shortName =
                    ((ProgramVariable) field).getProgramElementName().getProgramName();
                if ("length".equals(shortName)) {
                    final ExtList l = new ExtList();
                    l.add(changeList.get(0));
                    addChild(new ArrayLengthReference(l));
                } else {
                    String typeName =
                        ((ProgramVariable) x.getChildAt(1)).getKeYJavaType().getName();
                    typeName = PrettyPrinter.getTypeNameForAccessMethods(typeName);
                    addChild(new MethodReference(new ExtList(),
                        new ProgramElementName("_" + shortName + typeName),
                        (ReferencePrefix) changeList.get(0)));
                }
            }
        } else {
            String typeName = ((ProgramVariable) x.getChildAt(0)).getKeYJavaType().getName();
            typeName = PrettyPrinter.getTypeNameForAccessMethods(typeName);
            addChild(new MethodReference(new ExtList(),
                new ProgramElementName("_"
                    + ((ProgramVariable) changeList.get(0)).getProgramElementName().getProgramName()
                    + typeName),
                null));
        }
        changed();
    }
}
