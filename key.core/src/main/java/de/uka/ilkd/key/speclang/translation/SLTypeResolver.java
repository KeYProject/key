/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.translation;

import java.util.Objects;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.transformations.pipeline.PipelineConstants;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Resolves types occurring explicitly in specification expressions (e.g. as part of a static method
 * call MyClass.m()).
 */
@NullMarked
public final class SLTypeResolver extends SLExpressionResolver {

    public SLTypeResolver(JavaInfo javaInfo, SLResolverManager manager, KeYJavaType specInClass) {
        super(javaInfo, manager, specInClass);
    }


    @Override
    protected boolean canHandleReceiver(@Nullable SLExpression receiver) {
        return true;
    }


    @Override
    protected @Nullable SLExpression doResolving(@Nullable SLExpression receiver, String name,
            @Nullable SLParameters parameters) throws SLTranslationException {
        try {
            KeYJavaType type = javaInfo.getTypeByClassName(name, specInClass);
            if (type == null) {
                throw new SLTranslationException("Type " + name + " not found.");
            }
            return new SLExpression(type);
        } catch (RuntimeException e) {
            try {
                if (receiver != null) {
                    KeYJavaType containingType =
                        Objects.requireNonNull(receiver.getType(), "no receiver type");
                    while (true) {
                        String typeName = Objects
                                .requireNonNull(containingType.getSort(), "no containing type sort")
                                .name().toString();
                        if (typeName.substring(typeName.lastIndexOf('.') + 1).equals(name)) {
                            return new SLExpression(containingType);
                        }
                        ProgramVariable et = javaInfo.getAttribute(
                            PipelineConstants.IMPLICIT_ENCLOSING_THIS, containingType);
                        if (et != null) {
                            containingType =
                                Objects.requireNonNull(et.getKeYJavaType(), "no enclosing type");
                        } else {
                            break;
                        }
                    }
                }
            } catch (RuntimeException ex) {
            }
            // Type not found
            return null;
        }
    }
}
