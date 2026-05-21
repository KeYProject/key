/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;

/** 
 * This class is used to have a more or less equivalent representation of an annotation 
 * interface declaration as an interface declaration.
 *
 * @author PiIsRational 
 */
public class AnnotationInterfaceDeclarationNode extends ClassOrInterfaceDeclaration {

    public AnnotationInterfaceDeclarationNode() {
        super();
    }

    public AnnotationInterfaceDeclarationNode(AnnotationDeclaration ad) {
        setName(ad.getName().clone());

        var modifiers = new NodeList<Modifier>();
        for (var m : ad.modifiers()) {
            modifiers.add(m.clone());
        }
        setModifiers(modifiers);
        setInterface(true);

        var annotations = new NodeList<AnnotationExpr>();
        for (var annot : ad.annotations()) {
            annotations.add(annot.clone());
        }
        setAnnotations(annotations);

        if (ad.getComment().isPresent()) {
            setComment(ad.getComment().get().clone());
        }

        for (var m : ad.members()) { 
            addMember(m.clone());
        }
    }
}
