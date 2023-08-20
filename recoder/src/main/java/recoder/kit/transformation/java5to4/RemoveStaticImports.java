/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Type;
import recoder.convenience.Naming;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Import;
import recoder.java.ProgramElement;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.*;
import recoder.kit.MiscKit;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.UnitKit;

/**
 * Removes static imports from a given Compilation Unit and adds qualfication prefixes to (possible)
 * uses of such imports.
 *
 * @author Tobias Gutzmann
 * @since 0.80
 */
public class RemoveStaticImports extends TwoPassTransformation {
    private final CompilationUnit cu;
    private List<Item> hotSpots;
    private List<Import> statics;

    /**
     * @param sc
     */
    public RemoveStaticImports(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
        super(sc);
        this.cu = cu;
    }

    @Override
    public ProblemReport analyze() {
        hotSpots = new ArrayList<>();
        statics = new ArrayList<>();
        // are there any static imports at all?
        List<Import> il = cu.getImports();
        if (il == null || il.isEmpty()) {
            return IDENTITY;
        }
        for (Import im : il) {
            if (im.isStaticImport()) {
                statics.add(im);
            }
        }
        if (statics.isEmpty()) {
            return IDENTITY;
        }

        // traverse tree, consider member references only
        TreeWalker tw = new TreeWalker(cu);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof MemberReference && pe instanceof ReferenceSuffix
                    && pe instanceof NameReference) {
                MemberReference r = (MemberReference) pe;
                ReferenceSuffix s = (ReferenceSuffix) pe;
                NameReference nr = (NameReference) pe;
                if (s.getReferencePrefix() != null) {
                    continue; // not found through a static import
                }
                ClassType targetCT;
                if (r instanceof MethodReference) {
                    targetCT =
                        getSourceInfo().getMethod((MethodReference) r).getContainingClassType();
                } else if (r instanceof FieldReference) {
                    targetCT =
                        getSourceInfo().getField((FieldReference) r).getContainingClassType();
                } else if (r instanceof TypeReference) {
                    Type t = getSourceInfo().getType((TypeReference) r);
                    if (!(t instanceof ClassType)) {
                        continue;
                    }
                    targetCT = (ClassType) t;
                } else {
                    continue;
                }
                if (targetCT instanceof TypeDeclaration
                        && UnitKit.getCompilationUnit((TypeDeclaration) targetCT) == cu) {
                    continue;
                }
                String n = nr.getName();
                for (Import im : statics) {
                    TypeReference tr = im.getTypeReference(); // has to be set!
                    if (getSourceInfo().getType(tr) != targetCT) {
                        continue;
                    }
                    if (im.isMultiImport()) {
                        // TODO may still not be it... unlikely, but yet...
                        // (different type import may match)
                        // however, the way we currently handle this, no harm is done...
                    } else {
                        if (!n.equals(im.getStaticIdentifier().getText())) {
                            continue;
                        }
                        // TODO check: if another import matches, I *think*
                        // that should be a semantic error
                        // however, the way we currently handle this, no harm is done...
                    }
                    TypeReference prefix = im.getTypeReference();
                    hotSpots.add(new Item(nr, prefix));
                    break;
                }
            }
        }
        return super.analyze();
    }

    @Override
    public void transform() {
        super.transform();
        for (Import i : statics) {
            detach(i);
        }
        for (Item hs : hotSpots) {
            String x = Naming.toPathName(hs.prefix, hs.r.getName());
            if (x.startsWith("java.lang.")) {
                x = x.substring(10);
            }
            replace(hs.r, MiscKit.createUncollatedReferenceQualifier(getProgramFactory(), x));
        }
    }

    private static class Item {
        final NameReference r;
        final TypeReference prefix;

        Item(NameReference r, TypeReference prefix) {
            this.r = r;
            this.prefix = prefix;
        }
    }

}
