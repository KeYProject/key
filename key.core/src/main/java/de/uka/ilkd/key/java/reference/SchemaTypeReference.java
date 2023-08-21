/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.MatchConditions;


public class SchemaTypeReference extends TypeReferenceImp implements AbstractProgramElement {

    private final String fullName;

    public SchemaTypeReference(ProgramElementName name, int dimension, ReferencePrefix prefix) {
        super(name, dimension, prefix);
        final StringBuilder sb = new StringBuilder();

        // as no inner classes prefix must be package reference
        PackageReference rp = (PackageReference) prefix;
        while (rp != null) {
            sb.insert(0, rp.getName() + ".");
            rp = (PackageReference) rp.getReferencePrefix();
        }
        sb.append(name.toString());
        fullName = sb.toString();
    }

    public KeYJavaType getKeYJavaType() {
        return null;
    }

    public KeYJavaType getKeYJavaType(Services services) {
        KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(fullName);
        assert kjt != null
                : "KeYJavaType is null for SchemaTypeReference " + this + " - " + fullName;
        return kjt;
    }

    public ProgramElement getConcreteProgramElement(Services services) {
        return new TypeRef(getKeYJavaType(services));
    }

    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        ProgramElement t = source.getSource();
        if (t instanceof TypeReference) {
            if (getName().equals(((TypeReference) t).getName())
                    && ((TypeReference) t).getDimensions() == getDimensions()) {
                source.next();
                return matchCond;
            }
        }
        return null;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnAbstractProgramElement(this);
    }

}
