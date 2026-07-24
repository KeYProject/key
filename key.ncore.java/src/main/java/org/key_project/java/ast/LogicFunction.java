/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.java.ast;

public enum LogicFunction {
    Intersect(2, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\intersect")),
    SetUnion(2, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\set_union")),
    SetMinus(2, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\set_minus")),
    AllObjects(1, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\all_objects")),
    SeqPut(3, 1, PrimitiveType.JAVA_SEQ, AsFunction("\\seq_upd")),
    SeqGet(1, 1, PrimitiveType.JAVA_INT, AsArrayAccess()),
    SeqReverse(1, 1, PrimitiveType.JAVA_SEQ, AsFunction("\\seq_reverse")),
    AllFields(1, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\all_fields")),
    SeqIndexOf(2, 1, PrimitiveType.JAVA_INT, AsFunction("\\indexOf")),
    SeqSingleton(1, 1, PrimitiveType.JAVA_SEQ, AsFunction("\\seq_singleton")),
    SeqSub(3, 1, PrimitiveType.JAVA_SEQ, AsFunction("\\seq_sub")),
    SeqConcat(2, 1, PrimitiveType.JAVA_SEQ, AsFunction("\\seq_concat")),
    Singleton(1, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\singleton")),
    SeqLength(1, 1, PrimitiveType.JAVA_INT, AsSuffix("length"));

    public final int arity;
    public final int precedence;
    public final PrimitiveType returnType;
    public final PrettyPrinter.PrintOp format;

    LogicFunction(int arity, int precedence, PrimitiveType returnType,
            PrettyPrinter.PrintOp format) {
        this.arity = arity;
        this.precedence = precedence;
        this.returnType = returnType;
        this.format = format;
    }
}
