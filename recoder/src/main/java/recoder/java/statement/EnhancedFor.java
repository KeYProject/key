/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import java.util.List;

import recoder.java.LoopInitializer;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.VariableScope;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.util.Debug;

/**
 * @author gutzmann
 *         <p>
 *         This file is part of the RECODER library and protected by the LGPL.
 */
public class EnhancedFor extends LoopStatement implements VariableScope {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -4531341585909005502L;

    /**
     *
     */
    public EnhancedFor() {
        super();
    }

    /**
     * @param body
     */
    public EnhancedFor(Statement body) {
        super(body);
        makeParentRoleValid();
    }


    protected EnhancedFor(EnhancedFor proto) {
        super(proto);
        makeParentRoleValid();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.statement.LoopStatement#isExitCondition()
     */
    public boolean isExitCondition() {
        // TODO (?)
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.statement.LoopStatement#isCheckedBeforeIteration()
     */
    public boolean isCheckedBeforeIteration() {
        // TODO (?)
        return true;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.VariableScope#getVariablesInScope()
     */
    public List<VariableSpecification> getVariablesInScope() {
        LoopInitializer li = inits.get(0);
        return ((LocalVariableDeclaration) li).getVariables();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.VariableScope#getVariableInScope(java.lang.String)
     */
    public VariableSpecification getVariableInScope(String name) {
        VariableSpecification var = getVariablesInScope().get(0);
        if (var.getName().equals(name)) {
            return var;
        }
        /* else */
        return null;
    }

    /*
     * (non-Javadoc)
     *
     * @see
     * recoder.java.VariableScope#addVariableToScope(recoder.java.declaration.VariableSpecification)
     */
    public void addVariableToScope(VariableSpecification var) {
        Debug.assertNonnull(var);
        if (var != getVariablesInScope().get(0)) {
            throw new IllegalArgumentException();
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.VariableScope#removeVariableFromScope(java.lang.String)
     */
    public void removeVariableFromScope(@SuppressWarnings("unused") String name) {
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.ScopeDefiningElement#isDefinedScope()
     */
    public boolean isDefinedScope() {
        return true;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.ScopeDefiningElement#setDefinedScope(boolean)
     */
    public void setDefinedScope(@SuppressWarnings("unused") boolean defined) {
        // ignore.
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#accept(recoder.java.SourceVisitor)
     */
    public void accept(SourceVisitor v) {
        v.visitEnhancedFor(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#deepClone()
     */
    public EnhancedFor deepClone() {
        return new EnhancedFor(this);
    }

}
