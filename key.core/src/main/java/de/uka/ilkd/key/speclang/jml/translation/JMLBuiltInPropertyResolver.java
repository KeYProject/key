/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.jml.translation;

import java.util.Objects;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.speclang.translation.*;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * Resolver for built-in JML operators. Currently only handles array length.
 */
@NullMarked
public final class JMLBuiltInPropertyResolver extends SLExpressionResolver {

    private final SeqLDT seqLDT;


    public JMLBuiltInPropertyResolver(
            JavaInfo javaInfo, SLResolverManager manager,
            KeYJavaType specInClass) {
        super(javaInfo, manager, specInClass);
        this.seqLDT = services.getTypeConverter().getSeqLDT();
    }


    @Override
    protected boolean canHandleReceiver(@Nullable SLExpression receiver) {
        return receiver != null;
    }


    @Override
    protected @Nullable SLExpression doResolving(@Nullable SLExpression receiver, String name,
            @Nullable SLParameters parameters)
            throws SLTranslationException {
        if (parameters != null) {
            return null;
        }

        if (name.equals("length")) {
            SLExpression recv = Objects.requireNonNull(receiver, "no receiver");
            if (recv.isTerm()) {
                JTerm term = Objects.requireNonNull(recv.getTerm(), "no receiver term");
                if (term.sort().equals(seqLDT.targetSort())) {
                    return new SLExpression(services.getTermBuilder().seqLen(term),
                        javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT));
                }
            }
        }

        return null;
    }
}
