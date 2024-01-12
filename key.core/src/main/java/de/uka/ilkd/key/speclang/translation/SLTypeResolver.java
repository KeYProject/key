/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Resolves types occurring explicitly in specification expressions (e.g. as part of a static method
 * call MyClass.m()).
 */
public final class SLTypeResolver extends SLExpressionResolver {

    public SLTypeResolver(JavaInfo javaInfo, SLResolverManager manager, KeYJavaType specInClass) {
        super(javaInfo, manager, specInClass);
    }


    @Override
    protected boolean canHandleReceiver(SLExpression receiver) {
        return true;
    }


    @Override
    protected SLExpression doResolving(SLExpression receiver, String name, SLParameters parameters)
            throws SLTranslationException {
        try {
            KeYJavaType type = javaInfo.getTypeByClassName(name, specInClass);
            if (type == null) {
                throw new SLTranslationException("Type " + name + " not found.");
            }
            return new SLExpression(type);
        } catch (RuntimeException e) {
            try {
                if (receiver != null) {
                    KeYJavaType containingType = receiver.getType();
                    while (true) {
                        String typeName = containingType.getSort().name().toString();
                        if (typeName.substring(typeName.lastIndexOf('.') + 1).equals(name)) {
                            return new SLExpression(containingType);
                        }
                        ProgramVariable et = javaInfo.getAttribute(
                            ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, containingType);
                        if (et != null) {
                            containingType = et.getKeYJavaType();
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
