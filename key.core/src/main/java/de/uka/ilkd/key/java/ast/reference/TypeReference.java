/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.reference;

import de.uka.ilkd.key.java.ast.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;

/**
 * TypeReferences reference Types by name. A TypeReference can refer to
 * an outer or inner type and hence can also be a {@link MemberReference}, but does not have to. A
 * TypeReference can also occur as part of a reference path and as a prefix for types, too. As a
 * possible suffix for types, it can have other TypeReferences as a prefix, playing the role of a
 * {@link TypeReferenceContainer}.
 */
public interface TypeReference extends TypeReferenceInfix, TypeReferenceContainer,
        PackageReferenceContainer, MemberReference, NonTerminalProgramElement, SourceElement {

    String getName();

    ProgramElementName getProgramElementName();

    ReferencePrefix getReferencePrefix();

    int getDimensions();

    KeYJavaType getKeYJavaType();
}