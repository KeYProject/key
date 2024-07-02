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

package de.uka.ilkd.key.util.removegenerics;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.InterfaceDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.reference.FieldReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;

/**
 * 
 * A recoder transformation that removes all traces of Java5 generics from a
 * file.
 * 
 * It makes use of several sub-classes:
 * @author MU
 * 
 */

public class ResolveGenerics extends TwoPassTransformation {

    private CompilationUnit compUnitUnderTest;

    private List<TwoPassTransformation> transformations;

    /**
     * make a new generic resolver for a single compilation unit
     * 
     * @param sc
     *            Services to use (cross references!)
     * @param cu
     *            the unit under test
     */
    public ResolveGenerics(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
        super(sc);
        this.compUnitUnderTest = cu;
    }

    /**
     * Analyse a compilation unit to remove all traces of generic entities.
     * 
     * The problem is delegated to sub-classes for the following entities:
     * <ul>
     * <li>Class-/Interface-Declarations
     * <li>MethodDeclarations
     * <li>FieldDeclarations
     * </ul>
     * 
     * @see recoder.kit.TwoPassTransformation#analyze()
     */
    @Override
    public ProblemReport analyze() {
        TreeWalker tw = new TreeWalker(compUnitUnderTest);
        transformations = new LinkedList<TwoPassTransformation>();

        while (tw.next()) {

            ProgramElement pe = tw.getProgramElement();

            if (pe instanceof ClassDeclaration) {
                transformations.add(new ResolveTypeDeclaration((ClassDeclaration) pe, getServiceConfiguration()));
            } else

            if (pe instanceof InterfaceDeclaration) {
                transformations.add(new ResolveTypeDeclaration((InterfaceDeclaration) pe, getServiceConfiguration()));
            } else

            if (pe instanceof MethodDeclaration) {
                transformations.add(new ResolveMethodDeclaration((MethodDeclaration) pe, getServiceConfiguration()));
            } else

            if (pe instanceof MethodReference) {
                transformations.add(new ResolveMemberReference((MethodReference) pe, getServiceConfiguration()));
            } else

            if (pe instanceof FieldReference) {
                transformations.add(new ResolveMemberReference((FieldReference) pe, getServiceConfiguration()));
            } else

            if (pe instanceof VariableReference) {
                transformations.add(new ResolveMemberReference((VariableReference) pe, getServiceConfiguration()));
            } else

            if (pe instanceof TypeReference) {
                transformations.add(new ResolveTypeReference((TypeReference) pe, getServiceConfiguration()));
            }
        }

        Iterator<TwoPassTransformation> it = transformations.iterator();
        while (it.hasNext()) {
            TwoPassTransformation tpt = it.next();
            if (tpt.analyze() == IDENTITY)
                it.remove();
        }

        // perform transformations bottom up, so reverse the list
        Collections.reverse(transformations);

        if (transformations.isEmpty())
            return IDENTITY;
        else
            return EQUIVALENCE;
    }

    /**
     * simply iterate over all remaining transformations and apply them.
     */
    @Override
    public void transform() {
        for (TwoPassTransformation tpt : transformations)
            tpt.transform();
    }

    public CompilationUnit getCU() {
        return compUnitUnderTest;
    }
}