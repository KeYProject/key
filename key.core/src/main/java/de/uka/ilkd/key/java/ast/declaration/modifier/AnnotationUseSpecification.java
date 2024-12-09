/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration.modifier;

import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.declaration.Modifier;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.ast.reference.TypeReferenceContainer;

public class AnnotationUseSpecification extends Modifier implements TypeReferenceContainer {

    protected final TypeReference tr;

    public AnnotationUseSpecification(TypeReference tr) {
        super();
        this.tr = tr;
    }

    protected String getSymbol() {
        return "@" + tr.toString();
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (index == 0) {
            return tr;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getTypeReferenceCount() {
        return 1;
    }

    public ProgramElement getChildAt(int index) {
        if (index == 0) {
            return tr;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildCount() {
        return 1;
    }

}
