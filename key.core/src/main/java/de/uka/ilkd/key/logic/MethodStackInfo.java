/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.op.IProgramMethod;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public class MethodStackInfo implements NameCreationInfo {

    public static NameCreationInfo create(ProgramElement program) {
        return new MethodStackInfo(program);
    }

    private final ProgramElement element;


    public MethodStackInfo(ProgramElement element) {
        this.element = element;
    }

    /**
     * returns the method call stack
     */
    public ImmutableList<IProgramMethod> getMethodStack() {
        ImmutableList<IProgramMethod> list = ImmutableSLList.nil();
        if (element instanceof ProgramPrefix) {
            final ImmutableArray<ProgramPrefix> prefix =
                ((ProgramPrefix) element).getPrefixElements();
            for (int i = prefix.size() - 1; i >= 0; i--) {
                if (prefix.get(i) instanceof MethodFrame) {
                    final MethodFrame frame = (MethodFrame) prefix.get(i);
                    IProgramMethod method = frame.getProgramMethod();
                    if (method != null) {
                        list = list.prepend(method);
                    }
                }
            }
        }
        return list;
    }


    public String infoAsString() {
        StringBuilder result = new StringBuilder("Method stack:\n");

        for (IProgramMethod method : getMethodStack()) {
            result.append("- ").append(method.getProgramElementName().toString()).append("\n");
        }

        if (result.length() < 1) {
            return "";
        }

        result = new StringBuilder(result.substring(0, result.length() - 1));

        return result.toString();
    }



}
