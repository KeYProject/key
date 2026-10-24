/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.reference;

import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.MatchConditions;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
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

    public @Nullable KeYJavaType getKeYJavaType() {
        return null;
    }

    public KeYJavaType getKeYJavaType(Services services) {
        return Objects.requireNonNull(services.getJavaInfo().getKeYJavaType(fullName),
            "KeYJavaType is null for SchemaTypeReference " + this + " - " + fullName);
    }

    public ProgramElement getConcreteProgramElement(Services services) {
        return new TypeRef(getKeYJavaType(services));
    }

    public @Nullable MatchConditions match(SourceData source, @Nullable MatchConditions matchCond) {
        ProgramElement t = source.getSource();
        if (t instanceof TypeReference) {
            if (Objects.requireNonNull(getName()).equals(((TypeReference) t).getName())
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
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnAbstractProgramElement(this);
    }

}
