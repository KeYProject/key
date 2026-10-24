/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.declaration;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.abstraction.Variable;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Variable specification that defines a variable name. This is a part of a VariableDeclaration and
 * does not contain a type reference or own
 * modifiers. Note that calls to modifiers are delegated to the enclosing variable declaration and
 * are therefore discouraged. This was necessary to subtype Declaration as analyses are interested
 * in the exact location of a variable name.
 *
 * @author AL
 */

@NullMarked
public class VariableSpecification extends JavaNonTerminalProgramElement
        implements NamedProgramElement, ExpressionContainer, Variable {
    private static final Logger LOGGER = LoggerFactory.getLogger(VariableSpecification.class);

    /**
     * Initializer.
     */
    protected final @Nullable Expression initializer;

    /**
     * Dimensions.
     */
    protected final int dimensions;

    /**
     * the type
     */
    protected final Type type;

    protected final IProgramVariable programVariable;

    // The parameterless constructor deliberately leaves the {@code programVariable} and
    // {@code type} fields unset (null): it builds an "empty" variable specification whose
    // getters (see {@link #getType()}, {@link #getProgramVariable()}) are typed @NonNull by the
    // {@link de.uka.ilkd.key.java.ast.abstraction.Variable} resp.
    // {@link de.uka.ilkd.key.java.ast.abstraction.Field} interfaces. The null values are tolerated
    // at runtime by every accessor of this class.
    @SuppressWarnings("NullAway")
    public VariableSpecification() {
        this(null, 0, null, null, null);
    }

    // The {@code programVariable}'s KeYJavaType is null for schema program variables (see
    // ProgramSV.getKeYJavaType()); the resulting null {@code type} is stored by the delegate while
    // the delegated constructor's Type parameter stays @NonNull for the regular callers.
    @SuppressWarnings("NullAway")
    public VariableSpecification(IProgramVariable programVariable) {
        this(programVariable, programVariable.getKeYJavaType());
    }

    public VariableSpecification(IProgramVariable programVariable, Type type) {
        this(programVariable, 0, null, type, null);
    }


    public VariableSpecification(IProgramVariable programVariable, @Nullable Expression init,
            Type type) {
        this(programVariable, 0, init, type, null);
    }

    public VariableSpecification(IProgramVariable programVariable, int dim, Expression init,
            Type type) {
        this(programVariable, dim, init, type, PositionInfo.UNDEFINED);
    }

    public VariableSpecification(IProgramVariable programVariable, int dim,
            @Nullable Expression init,
            Type type,
            @Nullable PositionInfo pi) {
        super(pi);
        this.programVariable = programVariable;
        this.initializer = init;
        this.dimensions = dim;
        this.type = type;
    }


    /**
     * Constructor for the transformation of RECODER ASTs to KeY.
     *
     * @param children
     *        the children of this AST element as KeY classes. May contain: an Expression
     *        (as initializer of the variable) a Comment
     * @param dim
     *        the dimension of this type
     */
    public VariableSpecification(ExtList children, IProgramVariable programVariable, int dim,
            Type type) {
        super(children);
        this.programVariable = programVariable;
        initializer = children.get(Expression.class);
        dimensions = dim;
        this.type = type;
    }

    public VariableSpecification(PositionInfo pi, List<Comment> comments, Expression init,
            IProgramVariable programVariable, int dim, Type type) {
        super(pi, comments);
        this.programVariable = programVariable;
        initializer = init;
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
        if (programVariable != null) {
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
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException
     *         if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (programVariable != null) {
            if (index == 0) {
                return programVariable;
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
    public final @Nullable String getName() {
        return (programVariable == null) ? null : programVariable.name().toString();
    }

    /**
     * Get name.
     *
     * @return the name.
     */
    public ProgramElementName getProgramElementName() {
        if (programVariable.name() instanceof ProgramElementName) {
            return (ProgramElementName) programVariable.name();
        } else {
            return new ProgramElementName(programVariable.name().toString()); // only with SVs
        }
    }


    /**
     * Get program variable
     *
     * @return the program variable.
     */
    public IProgramVariable getProgramVariable() {
        return programVariable;
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
    public @Nullable Expression getInitializer() {
        return initializer;
    }


    public boolean isModel() {
        if (programVariable instanceof ProgramVariable pv) {
            return pv.isModel();
        }
        throw new UnsupportedOperationException(
            "Cannot determine if " + programVariable + " is a model field");
    }

    // Returns exactly whether an initializer is present (null-check on the honestly @Nullable
    // field). The field itself can legitimately stay null after a false return, so no
    // @EnsuresNonNull-style guarantee is (or can be) expressed here; callers must hold the
    // result of this method before invoking getInitializer().
    public boolean hasInitializer() {
        return initializer != null;
    }

    public boolean isFinal() {
        if (programVariable instanceof ProgramVariable pv) {
            return pv.isFinal();
        }
        throw new UnsupportedOperationException(
            "Cannot determine if " + programVariable + " is final");
    }


    public Type getType() {
        return type;
    }

    public String getFullName() {
        return Objects.requireNonNull(getName(), "name of the variable specification");
    }

    @Override
    public SourceElement getFirstElement() {
        return programVariable;
    }

    @Override
    public SourceElement getLastElement() {
        if (initializer != null) {
            return initializer.getLastElement();
        } else {
            return programVariable;
        }
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
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
    public @Nullable MatchConditions match(SourceData source, @Nullable MatchConditions matchCond) {
        final ProgramElement pe = source.getSource();
        matchCond = super.match(source, matchCond);
        if (matchCond != null
                && getDimensions() != ((VariableSpecification) Objects.requireNonNull(pe))
                        .getDimensions()) {
            return null;
        }
        return matchCond;
    }
}
