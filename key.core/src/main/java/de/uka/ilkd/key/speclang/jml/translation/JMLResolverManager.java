/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.translation.*;


/**
 * Resolver manager for JML.
 */
public final class JMLResolverManager extends SLResolverManager {

    public JMLResolverManager(JavaInfo javaInfo, KeYJavaType specInClass, ParsableVariable selfVar,
            SLExceptionFactory eManager) {
        super(eManager, specInClass, selfVar, false, javaInfo.getServices().getTermBuilder());
        addResolver(new JMLBuiltInPropertyResolver(javaInfo, this, specInClass));
        addResolver(new SLAttributeResolver(javaInfo, this, specInClass));
        addResolver(new SLMethodResolver(javaInfo, this, specInClass));
        addResolver(new SLTypeResolver(javaInfo, this, specInClass));
    }


    @Override
    public VisibilityModifier getSpecVisibility(MemberDeclaration md) {
        if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) md, "spec_public")) {
            return new Public();
        } else if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) md, "spec_protected")) {
            return new Protected();
        } else {
            return null;
        }
    }
}
