/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.convenience.TreeWalker;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.declaration.*;
import recoder.java.reference.TypeReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * Deals with annotations. Removes all annotation use specification and all annotation types, except
 * those, that are used as regular interfaces as well (which is bad coding style, however).<br>
 * WARNING: A target program may not compile after this transformation if any method that is
 * declared in java.lang.annotation.Annotation is referenced. Since this transformation is intended
 * for "downgrading" from Java5 to Java 1.4, that wouldn't work anyway.
 *
 * @author Tobias Gutzmann
 * @since 0.80
 */
public class RemoveAnnotations extends TwoPassTransformation {
    private final NonTerminalProgramElement root;
    private List<AnnotationUseSpecification> toRemove;
    private List<AnnotationDeclaration> unusedAnnotationTypes;
    private List<AnnotationDeclaration> usedAnnotationTypes;

    /**
     * @param sc
     */
    public RemoveAnnotations(CrossReferenceServiceConfiguration sc,
            NonTerminalProgramElement root) {
        super(sc);
        this.root = root;
    }

    @Override
    public ProblemReport analyze() {
        toRemove = new ArrayList<>(100);
        unusedAnnotationTypes = new ArrayList<>(10);
        usedAnnotationTypes = new ArrayList<>(10);
        TreeWalker tw = new TreeWalker(root);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof AnnotationUseSpecification) {
                toRemove.add((AnnotationUseSpecification) pe);
            } else if (pe instanceof AnnotationDeclaration) {
                AnnotationDeclaration ad = (AnnotationDeclaration) pe;
                List<TypeReference> trl =
                    getServiceConfiguration().getCrossReferenceSourceInfo().getReferences(ad);
                boolean remove = true;
                for (TypeReference typeReference : trl) {
                    if (!(typeReference.getASTParent() instanceof AnnotationUseSpecification)) {
                        remove = false;
                        break;
                    }
                }
                for (int i = 0; i < ad.getMembers().size(); i++) {
                    MemberDeclaration md = ad.getMembers().get(i);
                    if (md instanceof TypeDeclaration) {
                        // play it safely for now...
                        remove = false;
                        break;
                    }
                }
                if (remove) {
                    unusedAnnotationTypes.add(ad);
                } else {
                    usedAnnotationTypes.add(ad);
                }
            }
        }
        return super.analyze();
    }

    @Override
    public void transform() {
        super.transform();
        for (AnnotationUseSpecification au : toRemove) {
            detach(au);
        }
        for (AnnotationDeclaration ad : unusedAnnotationTypes) {
            detach(ad);
        }
        for (AnnotationDeclaration ad : usedAnnotationTypes) {
            replace(ad, makeInterface(ad));
        }
    }

    private InterfaceDeclaration makeInterface(AnnotationDeclaration ad) {
        ProgramFactory f = getProgramFactory();
        InterfaceDeclaration replacement = getProgramFactory().createInterfaceDeclaration();
        ASTList<MemberDeclaration> oldMems = ad.getMembers();
        ASTList<MemberDeclaration> newMems = new ASTArrayList<>(oldMems.size());
        for (MemberDeclaration md : oldMems) {
            MemberDeclaration newMD;
            if (md instanceof AnnotationPropertyDeclaration) {
                AnnotationPropertyDeclaration apd = (AnnotationPropertyDeclaration) md;
                MethodDeclaration m = f.createMethodDeclaration();
                if (apd.getComments() != null) {
                    m.setComments(apd.getComments().deepClone());
                }
                m.setIdentifier(apd.getIdentifier().deepClone());
                m.setTypeReference(apd.getTypeReference().deepClone());
                // everything else is not allowed to be set for annotation property declaration
                newMD = m;
            } else if (md instanceof AnnotationDeclaration) {
                // anntotation types marked for deletion have
                // already been deleted
                newMD = makeInterface((AnnotationDeclaration) md);
            } else {
                newMD = (MemberDeclaration) md.deepClone();
            }
            newMD.makeParentRoleValid();
            newMems.add(newMD);
        }
        replacement.setIdentifier(ad.getIdentifier().deepClone());
        replacement.setMembers(newMems);
        if (ad.getComments() != null) {
            replacement.setComments(ad.getComments().deepClone());
        }
        replacement.setDeclarationSpecifiers(ad.getDeclarationSpecifiers().deepClone());
        replacement.makeParentRoleValid();
        return replacement;
    }
}
