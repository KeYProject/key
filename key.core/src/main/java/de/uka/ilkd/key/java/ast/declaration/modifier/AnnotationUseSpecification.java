/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration.modifier;

import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.declaration.Modifier;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.ast.reference.TypeReferenceContainer;

import org.jspecify.annotations.NonNull;

public class AnnotationUseSpecification extends Modifier implements TypeReferenceContainer {

    protected final TypeReference typeReference;

    public AnnotationUseSpecification(TypeReference typeReference) {
        super();
        this.typeReference = typeReference;
    }

    protected @NonNull String getSymbol() {
        return "@" + typeReference.toString();
    }

    public @NonNull TypeReference getTypeReferenceAt(int index) {
        if (index == 0) {
            return typeReference;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getTypeReferenceCount() {
        return 1;
    }

    public @NonNull ProgramElement getChildAt(int index) {
        if (index == 0) {
            return typeReference;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildCount() {
        return 1;
    }

}
