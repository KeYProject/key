/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.metaconstruct;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.stmt.Statement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.rule.inst.SVInstantiations;

public abstract class ProgramTransformer implements Statement, Expr, RustyProgramElement {
    /** the name of the meta construct */
    private final Name name;
    /** the encapsulated program element */
    private final RustyProgramElement body;

    protected ProgramTransformer(Name name, RustyProgramElement body) {
        this.name = name;
        this.body = body;
    }

    /**
     * performs the program transformation needed for symbolic program transformation
     *
     * @param pe the RustyProgramElement on which the execution is performed
     * @param services the Services with all necessary information about the java programs
     * @param svInst the instantiations of the schemavariables
     * @return the transformated program
     */
    public abstract RustyProgramElement[] transform(RustyProgramElement pe, Services services,
            SVInstantiations svInst);

    /**
     * returns the name of the meta construct
     *
     * @return the name of the meta construct
     */
    public Name name() {
        return name;
    }

    public RustyProgramElement body() {
        return body;
    }

    @Override
    public Type type(Services services) {
        return null;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnProgramMetaConstruct(this);
    }

    @Override
    public SyntaxElement getChild(int n) {
        if (n == 0) {
            return body;
        }
        throw new IndexOutOfBoundsException();
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    /** to String */
    public String toString() {
        return name + "( " + body + ");";
    }
}
