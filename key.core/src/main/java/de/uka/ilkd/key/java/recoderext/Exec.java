/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.StatementContainer;
import recoder.java.VariableScope;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.java.statement.Branch;
import recoder.java.statement.BranchStatement;
import recoder.java.statement.Catch;
import recoder.list.generic.ASTList;
import recoder.util.Debug;

/**
 * An exec statement. Initial code copied from recoder's Try.
 *
 * @author Dominic Steinhöfel
 */
public class Exec extends BranchStatement implements StatementContainer, VariableScope {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -6939974882487466260L;

    /**
     * Body.
     */
    private StatementBlock body;

    /**
     * Branches.
     */
    private ASTList<Branch> branches;

    private ASTList<LocalVariableDeclaration> variableDeclarations;

    /**
     * Exec.
     */
    public Exec() {
        // nothing to do
    }

    /**
     * Exec.
     *
     * @param body a statement block.
     */

    public Exec(StatementBlock body) {
        setBody(body);
        makeParentRoleValid();
    }

    /**
     * Exec.
     *
     * @param body a statement block.
     * @param branches a branch mutable list.
     */
    public Exec(StatementBlock body, ASTList<Branch> branches) {
        setBranchList(branches);
        setBody(body);
        makeParentRoleValid();
    }

    /**
     * Exec.
     *
     * @param proto a Exec.
     */
    protected Exec(Exec proto) {
        super(proto);
        if (proto.body != null) {
            body = proto.body.deepClone();
        }
        if (proto.branches != null) {
            branches = proto.branches.deepClone();
        }
        if (proto.variableDeclarations != null) {
            variableDeclarations = proto.variableDeclarations.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */
    @Override
    public Exec deepClone() {
        return new Exec(this);
    }

    /**
     * Make parent role valid.
     */
    @Override
    public void makeParentRoleValid() {
        if (variableDeclarations != null) {
            for (LocalVariableDeclaration vd : variableDeclarations) {
                vd.setStatementContainer(this);
            }
        }
        if (body != null) {
            body.setStatementContainer(this);
        }
        if (branches != null) {
            for (int i = branches.size() - 1; i >= 0; i -= 1) {
                Branch b = branches.get(i);
                ((Ccatch) b).setParent(this);
            }
        }
    }

    @Override
    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    @Override
    public int getChildCount() {
        int result = 0;
        if (body != null) {
            result++;
        }
        if (branches != null) {
            result += branches.size();
        }
        result += variableDeclarations == null ? 0 : variableDeclarations.size();
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
        if (variableDeclarations != null) {
            if (index < variableDeclarations.size()) {
                return variableDeclarations.get(index);
            }
            index -= variableDeclarations.size();
        }
        if (body != null) {
            if (index == 0) {
                return body;
            }
            index--;
        }
        if (branches != null) {
            return branches.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public int getChildPositionCode(ProgramElement child) {
        // role 0: variable decls
        // role 1: body
        // role 2 (IDX): branch
        if (variableDeclarations != null) {
            int idx = variableDeclarations.indexOf(child);
            if (idx >= 0) {
                return (idx << 4);
            }
        }
        if (body == child) {
            return 1;
        }
        if (branches != null) {
            int index = branches.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 2;
            }
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
        int count;
        if (p == null) {
            throw new NullPointerException();
        }
        count = (variableDeclarations == null) ? 0 : variableDeclarations.size();
        for (int i = 0; i < count; i++) {
            if (variableDeclarations.get(i) == p) {
                if (q == null) {
                    variableDeclarations.remove(i);
                } else {
                    variableDeclarations.set(i, (LocalVariableDeclaration) q);
                    ((LocalVariableDeclaration) q).setStatementContainer(this);
                }
                return true;
            }
        }
        if (body == p) {
            StatementBlock r = (StatementBlock) q;
            body = r;
            if (r != null) {
                r.setStatementContainer(this);
            }
            return true;
        }
        count = (branches == null) ? 0 : branches.size();
        for (int i = 0; i < count; i++) {
            if (branches.get(i) == p) {
                if (q == null) {
                    branches.remove(i);
                } else {
                    branches.set(i, (Catch) q);
                    ((Ccatch) q).setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    /**
     * Get body.
     *
     * @return the statement block.
     */
    public StatementBlock getBody() {
        return body;
    }

    /**
     * Set body.
     *
     * @param body a statement block.
     */

    public void setBody(StatementBlock body) {
        this.body = body;
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
     * Get branch list.
     *
     * @return branches a branch mutable list.
     */

    public ASTList<Branch> getBranchList() {
        return branches;
    }

    /**
     * Set branch list.
     *
     * @param branches a branch mutable list.
     */
    public void setBranchList(ASTList<Branch> branches) {
        this.branches = branches;
    }

    /**
     * Get the number of branches in this container.
     *
     * @return the number of branches.
     */

    @Override
    public int getBranchCount() {
        return (branches != null) ? branches.size() : 0;
    }

    /*
     * Return the branch at the specified index in this node's "virtual" branch array. @param index
     * an index for a branch. @return the branch with the given index. @exception
     * ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */
    @Override
    public Branch getBranchAt(int index) {
        if (branches != null) {
            return branches.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public void accept(SourceVisitor v) {
        if (v instanceof SourceVisitorExtended) {
            ((SourceVisitorExtended) v).visitExec(this);
        } else {
            // throw new IllegalStateException(
            // "Method 'accept' not implemented in Exec");
        }
    }

    @Override
    public boolean isDefinedScope() {
        return true;
    }

    @Override
    public void setDefinedScope(boolean defined) {
        // ignore.
    }

    public ASTList<LocalVariableDeclaration> getVariableDeclarations() {
        return variableDeclarations;
    }

    public void setVariableDeclarations(ASTList<LocalVariableDeclaration> variableDeclarations) {
        this.variableDeclarations = variableDeclarations;
    }

    @Override
    public List<VariableSpecification> getVariablesInScope() {
        if (variableDeclarations != null) {
            List<VariableSpecification> res = new ArrayList<>();
            for (LocalVariableDeclaration vd : variableDeclarations) {
                res.addAll(vd.getVariables());
            }
            return res;
        }
        return Collections.emptyList();
    }

    @Override
    public VariableSpecification getVariableInScope(String name) {
        Debug.assertNonnull(name);
        for (VariableSpecification vs : getVariablesInScope()) {
            if (vs.getName().equals(name)) {
                return vs;
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

}
