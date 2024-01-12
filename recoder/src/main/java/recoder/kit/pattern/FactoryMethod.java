/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.pattern;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.ModelElement;
import recoder.ModelException;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.java.Identifier;
import recoder.java.Statement;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.kit.MethodKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * Not done yet: Should use semantical entities instead of syntactical ~Declarations.
 */
public class FactoryMethod implements DesignPattern {
    private static final Logger LOGGER = LoggerFactory.getLogger(FactoryMethod.class);

    private MethodDeclaration producer;

    private ConstructorDeclaration product;

    /**
     * Creates a new factory method using the given constructor. Given a constructor of the form
     *
     * <PRE>
     * <p>
     * [Modifiers] [Typename] ([Parameters]>) [Exceptions]
     *
     * </PRE>
     * <p>
     * the created producer looks like
     *
     * <PRE>
     * <p>
     * [Modifiers] [Typename] create[Typename]([Arguments]) [Exceptions] {
     * return new [Typename]([Arguments]); }
     *
     * </PRE>
     * <p>
     * where the [Arguments] have the same names as in the [Parameters] list.
     */
    public FactoryMethod(ConstructorDeclaration product) {
        if (product == null) {
            throw new IllegalArgumentException("A factory method requires a product method");
        }
        this.product = product;
        createProducer();
    }

    /**
     * Creates a factory method using the default constructor of the product.
     */
    public FactoryMethod(ClassDeclaration product) {
        if (product == null) {
            throw new IllegalArgumentException("A factory method requires a product");
        }
        try {
            this.product = product.getFactory()
                    .parseConstructorDeclaration("public " + product.getName() + "(){}");
        } catch (ParserException pe) {
            LOGGER.warn("Failed to parse method", pe);
        }
        createProducer();
    }

    public MethodDeclaration getProducer() {
        return producer;
    }

    public ConstructorDeclaration getProduct() {
        return product;
    }

    protected void createProducer() {
        ProgramFactory factory = product.getFactory();
        ConstructorDeclaration clone = null;
        try {
            clone = factory.parseConstructorDeclaration(product.toSource());
        } catch (ParserException pe) {
            LOGGER.warn("Failed to parse method", pe);
        }
        Identifier name = clone.getIdentifier();
        producer = factory.createMethodDeclaration(clone.getDeclarationSpecifiers(),
            factory.createTypeReference(name), factory.createIdentifier("create" + name.getText()),
            clone.getParameters(), clone.getThrown());
        ASTList<Statement> statements = new ASTArrayList<>(1);
        statements.add(factory.createReturn(MethodKit.createNew(clone)));
        producer.setBody(factory.createStatementBlock(statements));
    }

    /**
     * The validation ensures that a producer exists and that the return value of the producer
     * matches the product.
     */
    public void validate() throws ModelException {
        if (producer == null) {
            throw new InconsistentPatternException("Factory Method pattern requires a producer");
        }
        if (product == null) {
            throw new InconsistentPatternException("Factory Method pattern requires a product");
        }
        if (!producer.getReturnType().getName().equals(product.getMemberParent().getName())) {
            // could be allowed to create subtypes of return type
            throw new InconsistentPatternException(
                "Factory Method producer must create correct product type");
        }
    }

    /**
     * Get total number of participants.
     *
     * @return the number of participants.
     */
    public int getParticipantCount() {
        int res = 0;
        if (producer != null) {
            res += 1;
        }
        if (product != null) {
            res += 1;
        }
        return res;
    }

    /**
     * Get a participants by its index.
     *
     * @param index an index of a participant.
     * @return the participant.
     * @throws IndexOutOfBoundsException, if the index is not in bounds.
     */
    public ModelElement getParticipantAt(int index) {
        if (producer != null) {
            if (index == 0) {
                return producer;
            }
            index -= 1;
        }
        if (product != null) {
            if (index == 0) {
                return product;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }
}
