/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration.modifier;

import org.key_project.logic.SyntaxElement;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.reference.TypeReferenceContainer;

import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.rule.MatchConditions;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class AnnotationUseSpecification extends Modifier implements TypeReferenceContainer {
    private static final Logger LOGGER = LoggerFactory.getLogger(AnnotationUseSpecification.class);

    protected final TypeReference tr;

    public AnnotationUseSpecification(TypeReference tr) {
        super();
        this.tr = tr;
    }

    protected String getSymbol() {
        return "@" + tr.getName();
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

    @Override
    public SyntaxElement getChild(int index) {
        return getChildAt(index);
    }

    public int getChildCount() {
        return 1;
    }

    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement pe = source.getSource();
        matchCond = super.match(source, matchCond);

        if (matchCond != null && !tr.getName().equals(((AnnotationUseSpecification)pe).tr.getName())) {
            return null;
        }

        return matchCond;
    }
}
