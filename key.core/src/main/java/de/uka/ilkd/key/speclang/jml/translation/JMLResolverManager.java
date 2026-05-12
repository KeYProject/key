/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.ast.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.ast.declaration.Modifier;
import de.uka.ilkd.key.java.ast.declaration.ModifierKind;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.translation.*;


/**
 * Resolver manager for JML.
 */
public final class JMLResolverManager extends SLResolverManager {

    public JMLResolverManager(
            JavaInfo javaInfo, KeYJavaType specInClass, LocationVariable selfVar,
            SLExceptionFactory eManager) {
        super(eManager, specInClass, selfVar, javaInfo.getServices().getTermBuilder());
        addResolver(new JMLBuiltInPropertyResolver(javaInfo, this, specInClass));
        addResolver(new SLAttributeResolver(javaInfo, this, specInClass));
        addResolver(new SLMethodResolver(javaInfo, this, specInClass));
        addResolver(new SLTypeResolver(javaInfo, this, specInClass));
    }


    @Override
    public Modifier getSpecVisibility(MemberDeclaration md) {
        if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) md, ModifierKind.JML_SPEC_PUBLIC)) {
            return new Modifier(ModifierKind.PUBLIC);
        } else if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) md,
            ModifierKind.JML_SPEC_PROTECTED)) {
            return new Modifier(ModifierKind.PRIVATE);
        } else {
            return null;
        }
    }
}
