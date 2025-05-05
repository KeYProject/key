/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.abstraction.Variable;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.util.ExtList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * Variable specification that defines a variable name. This is a part of a
 * {@link recoder.java.declaration.VariableDeclaration} and does not contain a type reference or own
 * modifiers. Note that calls to modifiers are delegated to the enclosing variable declaration and
 * are therefore discouraged. This was necessary to subtype Declaration as analyses are interested
 * in the exact location of a variable name.
 *
 * @author AL
 */

public class VariableSpecification extends JavaNonTerminalProgramElement
        implements NamedProgramElement, ExpressionContainer, Variable {
    private static final Logger LOGGER = LoggerFactory.getLogger(VariableSpecification.class);

    /**
     * Initializer.
     */
    protected final Expression initializer;

    /**
     * Dimensions.
     */
    protected final int dimensions;

    /**
     * the type
     */
    protected final Type type;

    protected final IProgramVariable programVar;

    public VariableSpecification() {
        this(null, 0, null, null, null);
    }

    public VariableSpecification(IProgramVariable programVar) {
        this(programVar, programVar.getKeYJavaType());
    }

    public VariableSpecification(IProgramVariable programVar, Type type) {
        this(programVar, 0, null, type, null);
    }


    public VariableSpecification(IProgramVariable programVar, Expression init, Type type) {
        this(programVar, 0, init, type, null);
    }

    public VariableSpecification(IProgramVariable programVar, int dim, Expression init, Type type) {
        this(programVar, dim, init, type, PositionInfo.UNDEFINED);
    }

    public VariableSpecification(IProgramVariable programVar, int dim, Expression init, Type type,
            PositionInfo pi) {
        super(pi);
        this.programVar = programVar;
        this.initializer = init;
        this.dimensions = dim;
        this.type = type;
    }


    /**
     * Constructor for the transformation of RECODER ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: an Expression
     *        (as initializer of the variable) a Comment
     * @param dim the dimension of this type
     */
    public VariableSpecification(ExtList children, IProgramVariable programVar, int dim,
            Type type) {
        super(children);
        this.programVar = programVar;
        initializer = children.get(Expression.class);
        dimensions = dim;
        this.type = type;
    }


    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (programVar != null) {
            result++;
        }
        if (initializer != null) {
            result++;
        }
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (programVar != null) {
            if (index == 0) {
                return programVar;
            }
            index--;
        }
        if (initializer != null && index == 0) {
            return initializer;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    protected int computeHashCode() {
        return 37 * super.computeHashCode() + 31 * ((type == null) ? 0 : type.hashCode())
                + dimensions;
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    public int getExpressionCount() {
        return (initializer != null) ? 1 : 0;
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression array.
     *
     * @param index an index for an expression.
     *
     * @return the expression with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    public Expression getExpressionAt(int index) {
        if (initializer != null && index == 0) {
            return initializer;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get name.
     *
     * @return the string.
     */
    public final String getName() {
        return (programVar == null) ? null : programVar.name().toString();
    }

    /**
     * Get name.
     *
     * @return the name.
     */
    public ProgramElementName getProgramElementName() {
        if (programVar.name() instanceof ProgramElementName) {
            return (ProgramElementName) programVar.name();
        } else {
            return new ProgramElementName(programVar.name().toString()); // only with SVs
        }
    }


    /**
     * Get program variable
     *
     * @return the program variable.
     */
    public IProgramVariable getProgramVariable() {
        return programVar;
    }


    /**
     * Get dimensions.
     *
     * @return the int value.
     */
    public int getDimensions() {
        return dimensions;
    }

    /**
     * Get initializer.
     *
     * @return the expression.
     */
    public Expression getInitializer() {
        return initializer;
    }


    public boolean hasInitializer() {
        return initializer != null;
    }

    public boolean isFinal() {
        if (programVar instanceof ProgramVariable pv) {
            return pv.isFinal();
        }
        // This used to return always false.
        throw new UnsupportedOperationException("Cannot determine finality of " + programVar);
    }

    public boolean isModel() {
        if (programVar instanceof ProgramVariable pv) {
            return pv.isModel();
        }
        // This used to return always false.
        throw new UnsupportedOperationException("Cannot determine finality of " + programVar);
    }


    public Type getType() {
        return type;
    }

    public String getFullName() {
        return getName();
    }

    @Override
    public SourceElement getFirstElement() {
        return programVar;
    }

    @Override
    public SourceElement getLastElement() {
        if (initializer != null) {
            return initializer.getLastElement();
        } else {
            return programVar;
        }
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnVariableSpecification(this);
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }

        VariableSpecification vs = (VariableSpecification) o;

        if (dimensions != vs.getDimensions()) {
            return false;
        }
        if (type != null) {
            if (!(type.equals(vs.getType()))) {
                return false;
            }
        } else {
            if (vs.getType() != null) {
                return false;
            }
        }

        if (vs.getChildCount() != getChildCount()) {
            return false;
        }
        for (int i = 0, cc = getChildCount(); i < cc; i++) {
            if (!getChildAt(i).equals(vs.getChildAt(i))) {
                return false;
            }
        }
        return true;
    }

    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement pe = source.getSource();
        matchCond = super.match(source, matchCond);
        if (matchCond != null && getDimensions() != ((VariableSpecification) pe).getDimensions()) {
            return null;
        }
        return matchCond;
    }
}
