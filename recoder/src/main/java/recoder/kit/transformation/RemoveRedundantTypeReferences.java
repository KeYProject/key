/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Type;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.ProgramElement;
import recoder.java.declaration.Throws;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.expression.Operator;
import recoder.java.expression.operator.TypeCast;
import recoder.java.reference.ConstructorReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;
import recoder.service.SourceInfo;
import recoder.util.ProgressListener;
import recoder.util.ProgressListenerManager;

/**
 * Transformation that removes all redundant type references from a compilation unit or a series of
 * units.
 *
 * @author AL
 * @see recoder.kit.TypeKit#getRedundantSuperInterfaces
 * @see recoder.kit.TypeKit#getRedundantExceptions
 * @since 0.72
 */
public class RemoveRedundantTypeReferences extends TwoPassTransformation {

    private final List<CompilationUnit> units;

    private final List<TypeReference> references;

    private final boolean removeInterfaces;

    private final boolean removeExceptions;

    private final boolean removeTypeCasts;

    private final ProgressListenerManager listeners = new ProgressListenerManager(this);

    /**
     * Creates a new transformation object that removes redundant type references from
     * extends/implements and throws clauses and removes unnecessary type casts.
     *
     * @param sc the service configuration to use.
     */
    public RemoveRedundantTypeReferences(CrossReferenceServiceConfiguration sc) {
        this(sc, sc.getSourceFileRepository().getCompilationUnits(), true, true, true);
    }

    /**
     * Creates a new transformation object that removes redundant type references from
     * extends/implements and throws clauses.
     *
     * @param sc the service configuration to use.
     * @param list the compilation units that shall be stripped of references.
     * @param removeInterfaces switch that allows removal of superfluously inherited interface.
     * @param removeExceptions switch that allows removal of superfluously declared exceptions.
     * @param removeTypeCasts switch that allows removal of superfluously declared type casts.
     */
    public RemoveRedundantTypeReferences(CrossReferenceServiceConfiguration sc,
            List<CompilationUnit> list, boolean removeInterfaces, boolean removeExceptions,
            boolean removeTypeCasts) {
        super(sc);
        if (list == null) {
            throw new IllegalArgumentException("Missing units");
        }
        this.units = list;
        references = new ArrayList<>();
        this.removeInterfaces = removeInterfaces;
        this.removeExceptions = removeExceptions;
        this.removeTypeCasts = removeTypeCasts;
    }

    /**
     * Adds a progress listener for the analysis phase.
     */
    public void addProgressListener(ProgressListener l) {
        listeners.addProgressListener(l);
    }

    public void removeProgressListener(ProgressListener l) {
        listeners.removeProgressListener(l);
    }

    /**
     * Returns {@link #EQUIVALENCE}or {@link #IDENTITY}.
     *
     * @return the problem report.
     */
    public ProblemReport analyze() {
        SourceInfo si = getSourceInfo();
        listeners.fireProgressEvent(0, units.size(), "Checking Type References");
        for (int i = 0; i < units.size(); i += 1) {
            TreeWalker tw = new TreeWalker(units.get(i));
            while (tw.next()) {
                ProgramElement p = tw.getProgramElement();
                if (removeInterfaces && p instanceof TypeDeclaration) {
                    references
                            .addAll(TypeKit.getRedundantSuperInterfaces(si, ((TypeDeclaration) p)));
                } else if (removeExceptions && p instanceof Throws) {
                    references.addAll(TypeKit.getRedundantExceptions(si, (Throws) p));
                } else if (removeTypeCasts && p instanceof TypeCast) {
                    TypeCast tc = (TypeCast) p;
                    Type td = si.getType(tc.getTypeReference());
                    Type te = si.getType(tc.getExpressionAt(0));
                    ExpressionContainer parent = tc.getExpressionContainer();
                    if (parent instanceof MethodReference || parent instanceof ConstructorReference
                            || parent instanceof Operator) {
                        // might want to find out if there is overloading...
                        // this also applies to Operators!
                        if (te == td) {
                            references.add(tc.getTypeReference());
                        }
                    } else {
                        if (si.isWidening(te, td)) {
                            references.add(tc.getTypeReference());
                        }
                    }
                }
            }
            listeners.fireProgressEvent(i + 1);
        }
        return setProblemReport(references.isEmpty() ? IDENTITY : EQUIVALENCE);
    }

    /**
     * Removes the unnecessary type references.
     */
    public void transform() {
        super.transform();
        for (int i = references.size() - 1; i >= 0; i -= 1) {
            TypeReference tr = references.get(i);
            TypeReferenceContainer con = tr.getParent();
            if (!(con instanceof TypeCast)) {
                // might be either a Throws, or an InheritanceSpecification
                // that must be removed if the reference was the last child
                if (con.getChildCount() == 1) {
                    detach(con);
                } else {
                    detach(tr);
                }
            }
        }
        // second run for TypeCast, to avoid conflicts with cloned subtrees
        for (int i = references.size() - 1; i >= 0; i -= 1) {
            TypeReference tr = references.get(i);
            TypeReferenceContainer con = tr.getParent();
            if (con instanceof TypeCast) {
                Expression child = ((TypeCast) con).getExpressionAt(0);
                replace(con, child.deepClone());
            }
        }
    }

    /**
     * Returns the list of redundant type references.
     *
     * @return the list of type references that are/were superfluous.
     */
    public List<TypeReference> getTypeReferenceList() {
        return references;
    }

    /**
     * Returns the compilation units.
     *
     * @return the compilation units.
     */
    public List<CompilationUnit> getCompilationUnits() {
        return units;
    }
}
