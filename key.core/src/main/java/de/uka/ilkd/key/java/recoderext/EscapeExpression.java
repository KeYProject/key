/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.util.List;

import de.uka.ilkd.key.speclang.njml.JmlIO;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;
import recoder.list.generic.ASTArrayList;

/**
 * Handles JML expressions that begin with an escape character '\'.
 * <p>
 * Escaped identifiers in JML code are usually (always?) function symbols. JML function symbols
 * begin with an escape character, to distinguish them from Java function symbols that might occur
 * in an annotated source code.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class EscapeExpression extends Operator {

    /**
     * generated UID
     */
    private static final long serialVersionUID = -5679001759804380826L;

    protected final String functionName;

    /**
     * @return the functionName
     */
    public String getFunctionName() {
        return functionName;
    }

    protected EscapeExpression(String functionName, List<Expression> arguments) {
        this.functionName = functionName;
        children = new ASTArrayList<>(arguments);
    }

    public static EscapeExpression getEscapeExpression(String functionName,
            List<Expression> arguments) {
        if (functionName.startsWith("\\dl_")) {
            return new DLEmbeddedExpression(functionName.substring(4), arguments);
        } else if (JmlIO.isKnownFunction(functionName)) {
            return new RegisteredEscapeExpression(functionName, arguments);
        }
        throw new Error("Unknown escaped symbol used in JML code: " + functionName);
    }

    /**
     * Arity of an embedded JavaDL Expression depends upon the number of arguments.
     */
    @Override
    public int getArity() {
        return children.size();
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
    public void accept(SourceVisitor v) {
        // SourceVisitors in RecodeR currently are only used to perform the toSource() operation.
        // One of them needs to be implemented in order for source code to be reproduced.
    }

}
