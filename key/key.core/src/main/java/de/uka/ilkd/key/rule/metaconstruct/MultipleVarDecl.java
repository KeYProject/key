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
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Replaces a declaration of multiple variables by two variable declarations
 * where the first one declares a single variable and the second one the
 * remaining variables.
 */
public class MultipleVarDecl extends ProgramTransformer {

    public MultipleVarDecl(SchemaVariable sv) {
        super(new Name("multiple-var-decl"), (ProgramSV) sv);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        VariableDeclaration vardecl = (VariableDeclaration) pe;
        ImmutableArray<Modifier> modifiers = vardecl.getModifiers();
        TypeReference tref = vardecl.getTypeReference();
        ImmutableArray<? extends VariableSpecification> variables = vardecl
                .getVariables();
        VariableSpecification headVar = variables.get(0);
        VariableSpecification[] tailVars = new VariableSpecification[variables
                .size() - 1];

        for (int i = 0; i < variables.size() - 1; i++) {
            tailVars[i] = variables.get(i + 1);
        }

        if (pe instanceof LocalVariableDeclaration) {
            LocalVariableDeclaration newVarDecl = KeYJavaASTFactory
                    .declare(modifiers, tref, headVar);
            LocalVariableDeclaration newVarDeclList = KeYJavaASTFactory
                    .declare(modifiers, tref, tailVars);
            return new ProgramElement[] {
                KeYJavaASTFactory.block(newVarDecl, newVarDeclList) };
        }
        throw new RuntimeException("Meta-construct MultipleVarDecl could "
                + "not handle program element " + pe);
    }

}