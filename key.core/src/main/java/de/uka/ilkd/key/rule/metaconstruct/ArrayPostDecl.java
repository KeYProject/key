/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Objects;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.ast.declaration.Modifier;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;

/**
 * Replaces a local variable declaration <code> #t #v[]; </code> with <code>#t[] #v;</code>
 *
 * @author N/A
 */
@TransformerMeta(name = "#arrayPostDeclaration")
@NullMarked
public class ArrayPostDecl extends ProgramTransformer {

    public ArrayPostDecl(SchemaVariable sv) {
        super(new Name("#arrayPostDeclaration"), (ProgramSV) sv);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {

        final LocalVariableDeclaration declaration = (LocalVariableDeclaration) pe;
        final ImmutableArray<Modifier> modifiers = declaration.getModifiers();
        final TypeReference originalTypeReference = Objects.requireNonNull(
            declaration.getTypeReference(), "no type reference");

        final VariableSpecification var = declaration.getVariables().get(0);

        final IProgramVariable variable = var.getProgramVariable();
        // Build the new array type (#t[] #v) from the original type reference: increase the
        // dimension and keep the variable's base type. The initializer may be absent.
        final TypeRef newTypeRef =
            new TypeRef(originalTypeReference.getProgramElementName(),
                originalTypeReference.getAnnotations(),
                originalTypeReference.getDimensions() + var.getDimensions(),
                originalTypeReference.getReferencePrefix(),
                Objects.requireNonNull(variable.getKeYJavaType(),
                    "no KeYJavaType for variable " + variable));
        return new ProgramElement[] { KeYJavaASTFactory.declare(modifiers, variable,
            var.getInitializer(), newTypeRef) };
    }


    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of(body());
    }
}
