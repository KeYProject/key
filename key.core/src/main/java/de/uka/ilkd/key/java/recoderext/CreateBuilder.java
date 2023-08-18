/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Public;
import recoder.java.expression.literal.BooleanLiteral;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ThisReference;
import recoder.java.reference.TypeReference;
import recoder.java.statement.Return;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * If an allocation expression <code>new Class(...)</code> occurs, a new object has to be created,
 * in KeY this is quite similar to take it out of a list of objects and setting the implicit flag
 * <code> &lt;created&gt; </code> to <code>true</code> as well as setting all fields of the object
 * to their default values. For the complete procedure, the method creates the implicit method
 * <code>&lt;createObject$gt;</code> which on its part calls another implicit method
 * <code>lt;prepare&gt;</code> for setting the fields default values.
 */
public class CreateBuilder extends RecoderModelTransformer {

    public static final String IMPLICIT_CREATE = "<create>";

    public CreateBuilder(CrossReferenceServiceConfiguration services, TransformerCache cache) {
        super(services, cache);
    }

    /**
     * Creates the body of the static <code>&lt;createObject&gt;</code> method.
     */
    private StatementBlock createBody() {
        ASTList<Statement> result = new ASTArrayList<>(10);
        result.add(assign(
            attribute(new ThisReference(),
                new ImplicitIdentifier(ImplicitFieldAdder.IMPLICIT_INITIALIZED)),
            new BooleanLiteral(false)));

        result.add(new MethodReference(null,
            new ImplicitIdentifier(PrepareObjectBuilder.IMPLICIT_OBJECT_PREPARE_ENTER)));

        result.add(new Return(new ThisReference()));

        return new StatementBlock(result);
    }


    /**
     * creates the implicit static <code>&lt;createObject&gt;</code> method that takes the object to
     * be created out of the pool
     *
     * @param type the TypeDeclaration for which the <code>&lt;prepare&gt;</code> is created
     * @return the implicit <code>&lt;prepare&gt;</code> method
     */
    public MethodDeclaration createMethod(ClassDeclaration type) {
        ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<>(2);
        modifiers.add(new Public());

        MethodDeclaration md = new MethodDeclaration(modifiers, new TypeReference(getId(type)),
            new ImplicitIdentifier(IMPLICIT_CREATE), new ASTArrayList<>(0), null, createBody());
        md.makeAllParentRolesValid();
        return md;
    }


    /**
     * entry method for the constructor normalform builder
     *
     * @param td the TypeDeclaration
     */
    protected void makeExplicit(TypeDeclaration td) {
        if (td instanceof ClassDeclaration) {
            attach(createMethod((ClassDeclaration) td), td, td.getMembers().size());
        }
    }
}
