// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;

/**
 *  TypeReferences reference {@link recoder.abstraction.Type}s by name.
 *  A TypeReference can refer to an outer or inner type and hence can also
 *  be a {@link MemberReference}, but does not have to.
 *  A TypeReference can also occur as part of a reference path and
 *  as a prefix for types, too. As a possible suffix for types, it can
 *  have other TypeReferences as a prefix, playing the role of a
 *  {@link TypeReferenceContainer}.
 */
public interface TypeReference
 extends TypeReferenceInfix, TypeReferenceContainer, PackageReferenceContainer, MemberReference, NonTerminalProgramElement, SourceElement {

    String getName();

    ProgramElementName getProgramElementName();

    ReferencePrefix getReferencePrefix();

    int getDimensions();

    KeYJavaType getKeYJavaType();
}