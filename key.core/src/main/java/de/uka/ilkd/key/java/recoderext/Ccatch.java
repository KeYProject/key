/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

import recoder.java.ParameterContainer;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.VariableScope;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.java.statement.Branch;
import recoder.util.Debug;

/**
 * A ccatch statement (branch of exec statement). Initial code copied from recoder's Catch.
 *
 * @author Dominic Steinhöfel
 */
public class Ccatch extends Branch implements ParameterContainer, VariableScope {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -6747731923114431193L;

    /**
     * Parameter.
     */
    private Optional<ParameterDeclaration> parameter;

    private Optional<CcatchNonstandardParameterDeclaration> nonStdParameter;

    /**
     * Body.
     */
    private StatementBlock body;

    /**
     * Ccatch.
     */
    public Ccatch() {
        super();
        setParameterDeclaration(null);
        setNonStdParameterDeclaration(null);
    }

    /**
     * Ccatch.
     *
     * @param e a parameter declaration.
     * @param body a statement.
     */
    public Ccatch(ParameterDeclaration e, StatementBlock body) {
        super();
        setBody(body);
        setParameterDeclaration(e);
        setNonStdParameterDeclaration(null);
        makeParentRoleValid();
    }

    /**
     * Ccatch.
     *
     * @param e a parameter declaration.
     * @param body a statement.
     */
    public Ccatch(CcatchNonstandardParameterDeclaration e, StatementBlock body) {
        super();
        setBody(body);
        setNonStdParameterDeclaration(e);
        setParameterDeclaration(null);
        makeParentRoleValid();
    }

    /**
     * Ccatch.
     *
     * @param proto a Ccatch.
     */
    protected Ccatch(Ccatch proto) {
        super(proto);
        if (proto.hasParameterDeclaration()) {
            parameter = Optional.ofNullable(proto.parameter.get().deepClone());
        }
        if (proto.hasNonStdParameterDeclaration()) {
            nonStdParameter = Optional.ofNullable(proto.nonStdParameter.get().deepClone());
        }
        if (proto.body != null) {
            body = proto.body.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    @Override
    public Ccatch deepClone() {
        return new Ccatch(this);
    }

    /**
     * Make parent role valid.
     */
    @Override
    public void makeParentRoleValid() {
        parameter.ifPresent(p -> p.setParameterContainer(this));
        nonStdParameter.ifPresent(p -> p.setParameterContainer(this));
        if (body != null) {
            body.setStatementContainer(this);
        }
    }

    @Override
    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    @Override
    public int getChildCount() {
        int result = 0;
        if (hasParameterDeclaration()) {
            result++;
        }
        if (hasNonStdParameterDeclaration()) {
            result++;
        }
        if (body != null) {
            result++;
        }
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    @Override
    public ProgramElement getChildAt(int index) {
        if (hasParameterDeclaration()) {
            if (index == 0) {
                return parameter.get();
            }
            index--;
        }
        if (hasNonStdParameterDeclaration()) {
            if (index == 0) {
                return nonStdParameter.get();
            }
            index--;
        }
        if (body != null) {
            if (index == 0) {
                return body;
            }
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public int getChildPositionCode(ProgramElement child) {
        // role 0: parameter
        // role 1: body
        if (parameter.map(p -> p == child).orElse(false)) {
            return 0;
        }
        if (nonStdParameter.map(p -> p == child).orElse(false)) {
            return 0;
        }
        if (body == child) {
            return 1;
        }
        return -1;
    }

    /**
     * Replace a single child in the current node. The child to replace is matched by identity and
     * hence must be known exactly. The replacement element can be null - in that case, the child is
     * effectively removed. The parent role of the new child is validated, while the parent link of
     * the replaced child is left untouched.
     *
     * @param p the old child.
     * @param p the new child.
     * @return true if a replacement has occured, false otherwise.
     * @exception ClassCastException if the new child cannot take over the role of the old one.
     */
    @Override
    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        if (hasParameterDeclaration() && parameter.map(param -> param == p).orElse(false)) {
            ParameterDeclaration r = (ParameterDeclaration) q;
            parameter = Optional.of(r);
            if (r != null) {
                r.setParameterContainer(this);
            }
            return true;
        }
        if (hasNonStdParameterDeclaration()
                && nonStdParameter.map(param -> param == p).orElse(false)) {
            CcatchNonstandardParameterDeclaration r = (CcatchNonstandardParameterDeclaration) q;
            nonStdParameter = Optional.of(r);
            if (r != null) {
                r.setParameterContainer(this);
            }
            return true;
        }
        if (body == p) {
            StatementBlock r = (StatementBlock) q;
            body = r;
            if (r != null) {
                r.setStatementContainer(this);
            }
            return true;
        }
        return false;
    }

    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */
    @Override
    public int getStatementCount() {
        return (body != null) ? 1 : 0;
    }

    /*
     * Return the statement at the specified index in this node's "virtual" statement array. @param
     * index an index for a statement. @return the statement with the given index. @exception
     * ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */
    @Override
    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of parameters in this container.
     *
     * @return the number of parameters.
     */
    @Override
    public int getParameterDeclarationCount() {
        return (hasParameterDeclaration()) ? 1 : 0;
    }

    /*
     * Return the parameter declaration at the specified index in this node's "virtual" parameter
     * declaration array. @param index an index for a parameter declaration. @return the parameter
     * declaration with the given index. @exception ArrayIndexOutOfBoundsException if <tt> index
     * </tt> is out of bounds.
     */
    @Override
    public ParameterDeclaration getParameterDeclarationAt(int index) {
        if (hasParameterDeclaration() && index == 0) {
            return parameter.get();
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public CcatchNonstandardParameterDeclaration getNonstandardParameterDeclarationAt(int index) {
        if (hasNonStdParameterDeclaration() && index == 0) {
            return nonStdParameter.get();
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get body.
     *
     * @return the statement.
     */
    public Statement getBody() {
        return body;
    }

    /**
     * Set body.
     *
     * @param statement a statement.
     */
    public void setBody(Statement statement) {
        body = (StatementBlock) statement;
    }

    /**
     * Set parent.
     *
     * @param parent a try.
     */
    public void setParent(Exec parent) {
        this.parent = parent;
    }

    public boolean hasParameterDeclaration() {
        return parameter.isPresent();
    }

    public boolean hasNonStdParameterDeclaration() {
        return nonStdParameter.isPresent();
    }

    /**
     * Get parameter declaration.
     *
     * @return the parameter declaration.
     */
    public ParameterDeclaration getParameterDeclaration() {
        return parameter.orElse(null);
    }

    /**
     * Get parameter declaration.
     *
     * @return the parameter declaration.
     */
    public CcatchNonstandardParameterDeclaration getNonStdParameterDeclaration() {
        return nonStdParameter.orElse(null);
    }

    /**
     * Set parameter declaration.
     *
     * @param p a parameter declaration.
     */
    public void setParameterDeclaration(ParameterDeclaration p) {
        parameter = Optional.ofNullable(p);
    }

    /**
     * Set parameter declaration.
     *
     * @param p a parameter declaration.
     */
    public void setNonStdParameterDeclaration(CcatchNonstandardParameterDeclaration p) {
        nonStdParameter = Optional.ofNullable(p);
    }

    @Override
    public boolean isDefinedScope() {
        return true;
    }

    @Override
    public void setDefinedScope(boolean defined) {
        // ignore
    }

    @Override
    public List<VariableSpecification> getVariablesInScope() {
        if (hasParameterDeclaration()) {
            return parameter.map(ParameterDeclaration::getVariables).orElse(null);
        } else if (nonStdParameter.map(p -> p instanceof CcatchReturnValParameterDeclaration)
                .orElse(false)) {
            return nonStdParameter.map(CcatchReturnValParameterDeclaration.class::cast)
                    .map(CcatchReturnValParameterDeclaration::getDelegate)
                    .map(ParameterDeclaration::getVariables).orElse(null);
        }

        return Collections.emptyList();
    }

    @Override
    public VariableSpecification getVariableInScope(String name) {
        if (hasParameterDeclaration()) {
            VariableSpecification v =
                parameter.map(ParameterDeclaration::getVariableSpecification).orElse(null);
            if (name.equals(v.getName())) {
                return v;
            }
        } else if (nonStdParameter.map(p -> p instanceof CcatchReturnValParameterDeclaration)
                .orElse(false)) {
            VariableSpecification v =
                nonStdParameter.map(CcatchReturnValParameterDeclaration.class::cast)
                        .map(CcatchReturnValParameterDeclaration::getDelegate)
                        .map(ParameterDeclaration::getVariableSpecification).orElse(null);
            if (name.equals(v.getName())) {
                return v;
            }
        }

        return null;
    }

    @Override
    public void addVariableToScope(VariableSpecification var) {
        Debug.assertNonnull(var);
    }

    @Override
    public void removeVariableFromScope(String name) {
        Debug.assertNonnull(name);
    }

    @Override
    public void accept(SourceVisitor v) {
        if (v instanceof SourceVisitorExtended) {
            ((SourceVisitorExtended) v).visitCcatch(this);
        } else {
            // throw new IllegalStateException(
            // "Method 'accept' not implemented in Ccatch");
        }
    }
}
