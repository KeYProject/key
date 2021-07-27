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

package de.uka.ilkd.key.rule.metaconstruct;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Replaces a local variable declaration <code> #t #v[]; </code> with
 * <code>#t[] #v;</code>
 *
 * @author N/A
 */
public class ArrayPostDecl extends ProgramTransformer {

    public ArrayPostDecl(SchemaVariable sv) {
        super(new Name("array-post-declaration"), (ProgramSV) sv);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {

        final LocalVariableDeclaration declaration = (LocalVariableDeclaration) pe;
        final ImmutableArray<Modifier> modifiers = declaration.getModifiers();
        final TypeReference originalTypeReference = declaration
                .getTypeReference();

        final VariableSpecification var = declaration.getVariables().get(0);

        final IProgramVariable variable = var.getProgramVariable();
        return new ProgramElement[] {
            KeYJavaASTFactory.declare(modifiers, variable, var.getInitializer(),
                originalTypeReference.getProgramElementName(),
                originalTypeReference.getDimensions() + var.getDimensions(),
                originalTypeReference.getReferencePrefix(),
                variable.getKeYJavaType()) };
    }

}