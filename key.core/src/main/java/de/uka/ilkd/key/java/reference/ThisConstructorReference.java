package de.uka.ilkd.key.java.reference;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;


/**
 * This constructor reference.
 */
public class ThisConstructorReference extends SpecialConstructorReference {

    /**
     * This constructor reference.
     */
    public ThisConstructorReference() {
        super();
    }


    /**
     * This constructor reference.
     *
     * @param arguments an expression mutable list.
     */
    public ThisConstructorReference(Expression[] arguments) {
        super(arguments);
    }


    /**
     * This constructor reference.
     *
     * @param arguments an expression mutable list.
     */
    public ThisConstructorReference(ImmutableArray<Expression> arguments) {
        super(arguments);
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: several of
     *        Expression (as initializers of the array), Comments Must contain: execution context
     */
    public ThisConstructorReference(ExtList children) {
        super(children);
    }


    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    @Override
    public void visit(Visitor v) {
        v.performActionOnThisConstructorReference(this);
    }


    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printThisConstructorReference(this);
    }


    @Override
    public ReferencePrefix getReferencePrefix() {
        return null;
    }
}
