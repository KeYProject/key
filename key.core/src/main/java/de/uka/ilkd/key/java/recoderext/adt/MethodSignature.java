/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Identifier;
import recoder.java.JavaNonTerminalProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

public class MethodSignature extends JavaNonTerminalProgramElement {

    private static final long serialVersionUID = 6966957683489654730L;
    private final Identifier methodName;
    private final ASTList<TypeReference> paramTypes;

    public MethodSignature(Identifier methodName, ASTList<TypeReference> paramTypes) {
        super();
        this.methodName = methodName;
        this.paramTypes = paramTypes;
    }

    @Override
    public ProgramElement getChildAt(int i) {
        if (i == 0) {
            return methodName;
        }
        i--;
        if (i >= 0 && i < paramTypes.size()) {
            return paramTypes.get(i);
        }
        return null;
    }

    @Override
    public int getChildCount() {
        return 1 + paramTypes.size();
    }

    @Override
    public int getChildPositionCode(ProgramElement child) {
        if (child == methodName) {
            return 0;
        }
        int idx = paramTypes.indexOf(child);
        return idx < 0 ? -1 : idx + 1;
    }

    @Override
    public boolean replaceChild(ProgramElement arg0, ProgramElement arg1) {
        return false;
    }

    @Override
    public NonTerminalProgramElement getASTParent() {
        return null;
    }

    @Override
    public void accept(SourceVisitor arg0) {
    }

    @Override
    public SourceElement deepClone() {
        throw new IllegalStateException("Not implemented in " + "MethodSignature");
    }


    public Identifier getMethodName() {
        return methodName;
    }

    public ASTList<TypeReference> getParamTypes() {
        return paramTypes;
    }
}
