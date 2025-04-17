/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.Field;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.util.ExtList;

/*
 * FieldSpecification taken from COMPOST and changed to achieve an immutable structure
 */

public class FieldSpecification extends VariableSpecification implements Field {

    /**
     * Field specification.
     */

    public FieldSpecification() {}

    public FieldSpecification(IProgramVariable var) {
        this(var, var.getKeYJavaType());
    }

    /**
     * Field specification.
     *
     * @param var
     *        the ProgramVariable representing this concrete field
     * @param type
     *        the Type of this field
     */

    public FieldSpecification(IProgramVariable var, Type type) {
        super(var, type);
    }

    /**
     * Field specification.
     *
     * @param var
     *        the ProgramVariable representing this concrete field
     * @param init
     *        the Expression the field is initialised with.
     * @param type
     *        the Type of this field
     */

    public FieldSpecification(ProgramVariable var, Expression init, Type type) {
        super(var, init, type);
    }

    /**
     * Field specification.
     *
     * @param var
     *        the ProgramVariable representing this concrete field
     * @param dimensions
     *        an int defining the dimension
     * @param init
     *        the Expression the field is initialised with.
     * @param type
     *        the Type of this field
     */
    public FieldSpecification(ProgramVariable var, int dimensions, Expression init, Type type) {
        super(var, dimensions, init, type, null);
    }


    /**
     * Field specification.
     *
     * @param children
     *        an ExtList with the children. May contain: an Expression (as initializer of
     *        the variable) a ProgramElementName (as name of the variable) a Comment
     * @param var
     *        the ProgramVariable representing this concrete field
     * @param dimensions
     *        an int defining the dimension
     * @param type
     *        the Type of this field
     */

    public FieldSpecification(ExtList children, ProgramVariable var, int dimensions, Type type) {
        super(children, var, dimensions, type);
    }

    public FieldSpecification(PositionInfo pi, List<Comment> comments, Expression init,
            IProgramVariable var, int dim, Type type) {
        super(pi, comments, init, var, dim, type);
    }

    /**
     * returns the name of the field as used in programs. In the logic each field has a unique name
     * which is composed by the class name where it is declared and its source code name
     *
     * @return returns the name of the field as used in programs
     */
    public String getProgramName() {
        return getProgramElementName().getProgramName();
    }

    /**
     * Test whether the declaration is static.
     */
    public boolean isStatic() {
        return ((ProgramVariable) programVariable).isStatic();
    }

    /**
     * Test whether the declaration is private.
     */
    public boolean isPrivate() {
        return false;
    }

    /**
     * Test whether the declaration is protected.TO BE IMPLEMENTED
     */

    public boolean isProtected() {
        return false;
    }

    /**
     * Test whether the declaration is public.TO BE IMPLEMENTED
     */

    public boolean isPublic() {
        return false;
    }


    /**
     * Test whether the declaration is transient.TO BE IMPLEMENTED
     */

    public boolean isTransient() {
        return false;
    }

    /**
     * Test whether the declaration is volatile.TO BE IMPLEMENTED
     */

    public boolean isVolatile() {
        return false;
    }

    /**
     * Test whether the declaration is strictFp.TO BE IMPLEMENTED
     */
    public boolean isStrictFp() {
        return false;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnFieldSpecification(this);
    }

    @Override
    public boolean isImplicit() {
        return programVariable instanceof ProgramVariable
                && ((ProgramVariable) programVariable).isImplicit();
    }

}
