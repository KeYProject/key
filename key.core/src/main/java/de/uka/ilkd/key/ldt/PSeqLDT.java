/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.ExtList;

import org.jspecify.annotations.Nullable;

public final class PSeqLDT extends ParametricLDT {
    public static final Name NAME = new Name("PSeq");

    private final ParametricFunctionDecl pseqGet;
    private final ParametricFunctionDecl pseqLen;
    private final ParametricFunctionDecl pseqIndexOf;
    private final ParametricFunctionDecl pseqGetOutside;
    private final ParametricFunctionDecl pseqEmpty;
    private final ParametricFunctionDecl pseqSingleton;
    private final ParametricFunctionDecl pseqConcat;
    private final ParametricFunctionDecl pseqSub;
    private final ParametricFunctionDecl pseqReverse;
    private final ParametricFunctionDecl pseqUpd;
    private final ParametricFunctionDecl pseqDef;
    private final ParametricFunctionDecl pseqSwap;
    private final ParametricFunctionDecl pseqRemove;

    private final Function pseqNPermInv;


    public PSeqLDT(TermServices services) {
        super(NAME, services);

        pseqGet = addParametricFunction(services, "pseqGet");
        pseqLen = addParametricFunction(services, "pseqLen");
        pseqIndexOf = addParametricFunction(services, "pseqIndexOf");
        pseqGetOutside = addParametricFunction(services, "pseqGetOutside");
        pseqEmpty = addParametricFunction(services, "pseqEmpty");
        pseqSingleton = addParametricFunction(services, "pseqSingleton");
        pseqConcat = addParametricFunction(services, "pseqConcat");
        pseqSub = addParametricFunction(services, "pseqSub");
        pseqReverse = addParametricFunction(services, "pseqReverse");
        pseqUpd = addParametricFunction(services, "pseqUpd");
        pseqDef = addParametricFunction(services, "pseqDef");
        pseqSwap = addParametricFunction(services, "pseqSwap");
        pseqRemove = addParametricFunction(services, "pseqRemove");
        pseqNPermInv = addFunction(services, "pseqNPermInv");
    }

    public ParametricFunctionDecl getPseqGet() {
        return pseqGet;
    }

    public ParametricFunctionDecl getPseqLen() {
        return pseqLen;
    }

    public ParametricFunctionDecl getPseqIndexOf() {
        return pseqIndexOf;
    }

    public ParametricFunctionDecl getPseqGetOutside() {
        return pseqGetOutside;
    }

    public ParametricFunctionDecl getPseqEmpty() {
        return pseqEmpty;
    }

    public ParametricFunctionDecl getPseqSingleton() {
        return pseqSingleton;
    }

    public ParametricFunctionDecl getPseqConcat() {
        return pseqConcat;
    }

    public ParametricFunctionDecl getPseqSub() {
        return pseqSub;
    }

    public ParametricFunctionDecl getPseqReverse() {
        return pseqReverse;
    }

    public ParametricFunctionDecl getPseqUpd() {
        return pseqUpd;
    }

    public ParametricFunctionDecl getPseqDef() {
        return pseqDef;
    }

    public ParametricFunctionDecl getPseqSwap() {
        return pseqSwap;
    }

    public ParametricFunctionDecl getPseqRemove() {
        return pseqRemove;
    }

    public Function getPseqNPermInv() {
        return pseqNPermInv;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm[] subs, Services services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm left, JTerm right, Services services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, JTerm sub, TermServices services,
            ExecutionContext ec) {
        return false;
    }

    @Override
    public JTerm translateLiteral(Literal lit, Services services) {
        return null;
    }

    @Override
    public @Nullable Function getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }

    @Override
    public Expression translateTerm(JTerm t, ExtList children, Services services) {
        return null;
    }
}
