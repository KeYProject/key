/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.speclang.translation.*;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;


/**
 * Resolver for built-in JML operators. Currently only handles array length.
 */
public final class JMLBuiltInPropertyResolver extends SLExpressionResolver {

    private final @NonNull SeqLDT seqLDT;


    public JMLBuiltInPropertyResolver(@NonNull JavaInfo javaInfo,
            @NonNull SLResolverManager manager,
            @NonNull KeYJavaType specInClass) {
        super(javaInfo, manager, specInClass);
        this.seqLDT = services.getTypeConverter().getSeqLDT();
    }


    @Override
    protected boolean canHandleReceiver(@Nullable SLExpression receiver) {
        return receiver != null;
    }


    @Override
    protected SLExpression doResolving(@NonNull SLExpression receiver, @NonNull String name,
            @Nullable SLParameters parameters)
            throws SLTranslationException {
        if (parameters != null) {
            return null;
        }

        if (name.equals("length") && receiver.isTerm()
                && receiver.getTerm().sort().equals(seqLDT.targetSort())) {
            return new SLExpression(services.getTermBuilder().seqLen(receiver.getTerm()),
                javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT));
        }

        return null;
    }
}
