/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.ArrayLengthReference;
import de.uka.ilkd.key.java.ast.reference.FieldReference;
import de.uka.ilkd.key.java.ast.reference.MethodReference;
import de.uka.ilkd.key.java.ast.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.PrettyPrinter;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Replaces field references o.a by methodcalls o._a(). This is needed for unit test generation.
 */
@NullMarked
public class FieldReplaceVisitor extends CreatingASTVisitor {

    private @Nullable ProgramElement result = null;

    // private KeYJavaType containingKJT=null

    public FieldReplaceVisitor(final ProgramElement pe, final Services services) {
        super(pe, true, services);
    }

    /** starts the walker */
    @Override
    public void start() {
        stack.push(new ExtList());
        walk(root());
        final ExtList el = stack.getFirst();
        int i = 0;
        while (!(el.get(i) instanceof ProgramElement)) {
            i++;
        }
        result = (ProgramElement) stack.getFirst().get(i);
    }

    public @Nullable ProgramElement result() {
        return result;
    }

    @Override
    /**
     * Replaces the given field reference by the corresponding access-method or array-length
     * reference.
     * <p>
     * The program variable of a generalized field reference is always present; the dereferences
     * of the (nullable) program variable are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public void performActionOnFieldReference(final FieldReference x) {
        final ExtList changeList = stack.getFirst();
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
                        x.getProgramVariable().getKeYJavaType().getName();
                    typeName = PrettyPrinter.getTypeNameForAccessMethods(typeName);
                    addChild(new MethodReference(new ExtList(),
                        new ProgramElementName("_" + shortName + typeName),
                        (ReferencePrefix) changeList.get(0)));
                }
            }
        } else {
            String typeName = x.getProgramVariable().getKeYJavaType().getName();
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
