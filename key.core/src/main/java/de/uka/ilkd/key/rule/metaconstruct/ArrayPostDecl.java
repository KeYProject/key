/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

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

import org.key_project.util.collection.ImmutableArray;

/**
 * Replaces a local variable declaration <code> #t #v[]; </code> with <code>#t[] #v;</code>
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
        final TypeReference originalTypeReference = declaration.getTypeReference();

        final VariableSpecification var = declaration.getVariables().get(0);

        final IProgramVariable variable = var.getProgramVariable();
        return new ProgramElement[] { KeYJavaASTFactory.declare(modifiers, variable,
            var.getInitializer(), originalTypeReference.getProgramElementName(),
            originalTypeReference.getDimensions() + var.getDimensions(),
            originalTypeReference.getReferencePrefix(), variable.getKeYJavaType()) };
    }

}
