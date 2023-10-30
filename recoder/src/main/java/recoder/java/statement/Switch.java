/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import recoder.abstraction.ClassType;
import recoder.java.*;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.list.generic.ASTList;
import recoder.util.Debug;

/**
 * Switch.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Switch extends BranchStatement
        implements ExpressionContainer, VariableScope, TypeScope {

    /**
     * Undefined scope tag.
     */

    protected final static Map UNDEFINED_SCOPE = new HashMap(1);
    /**
     * serialization id
     */
    private static final long serialVersionUID = 1L;
    /**
     * Branches.
     */

    protected ASTList<Branch> branches;
    /**
     * Expression.
     */

    protected Expression expression;
    /**
     * Scope table for types.
     */

    @SuppressWarnings("unchecked")
    protected Map<String, TypeDeclaration> name2type = UNDEFINED_SCOPE;

    /**
     * Scope table for fields.
     */

    @SuppressWarnings("unchecked")
    protected Map<String, VariableSpecification> name2var = UNDEFINED_SCOPE;

    /**
     * Switch.
     */

    public Switch() {
        // nothing to do
    }

    /**
     * Switch.
     *
     * @param e an expression.
     */

    public Switch(Expression e) {
        setExpression(e);
        makeParentRoleValid();
    }

    /**
     * Switch.
     *
     * @param e an expression.
     * @param branches a branch mutable list.
     */

    public Switch(Expression e, ASTList<Branch> branches) {
        setBranchList(branches);
        setExpression(e);
        makeParentRoleValid();
    }

    /**
     * Switch.
     *
     * @param proto a switch.
     */

    protected Switch(Switch proto) {
        super(proto);
        if (proto.expression != null) {
            expression = proto.expression.deepClone();
        }
        if (proto.branches != null) {
            branches = proto.branches.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Switch deepClone() {
        return new Switch(this);
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (expression != null) {
            result++;
        }
        if (branches != null) {
            result += branches.size();
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
        if (expression != null) {
            if (index == 0) {
                return expression;
            }
            index--;
        }
        if (branches != null) {
            return branches.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: expression
        // role 1 (IDX): branch
        if (expression == child) {
            return 0;
        }
        if (branches != null) {
            int index = branches.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 1;
            }
        }
        return -1;
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (expression != null) {
            expression.setExpressionContainer(this);
        }
        if (branches != null) {
            for (int i = branches.size() - 1; i >= 0; i -= 1) {
                Branch b = branches.get(i);
                if (b instanceof Case) {
                    ((Case) b).setParent(this);
                } else {
                    ((Default) b).setParent(this);
                }
            }
        }
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
     * @throws ClassCastException if the new child cannot take over the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        int count;
        if (p == null) {
            throw new NullPointerException();
        }
        if (expression == p) {
            Expression r = (Expression) q;
            expression = r;
            if (r != null) {
                r.setExpressionContainer(this);
            }
            return true;
        }
        count = (branches == null) ? 0 : branches.size();
        for (int i = 0; i < count; i++) {
            if (branches.get(i) == p) {
                if (q == null) {
                    branches.remove(i);
                } else {
                    if (q instanceof Case) {
                        branches.set(i, (Case) q);
                        ((Case) q).setParent(this);
                    } else {
                        branches.set(i, (Default) q);
                        ((Default) q).setParent(this);
                    }
                }
                return true;
            }
        }
        return false;
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    public int getExpressionCount() {
        return (expression != null) ? 1 : 0;
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression
     * array. @param index an index for an expression. @return the expression with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Expression getExpressionAt(int index) {
        if (expression != null && index == 0) {
            return expression;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get expression.
     *
     * @return the expression.
     */

    public Expression getExpression() {
        return expression;
    }

    /**
     * Set expression.
     *
     * @param e an expression.
     */

    public void setExpression(Expression e) {
        if (e == null) {
            throw new NullPointerException("Switches must have an expression");
        }
        expression = e;
    }

    /**
     * Get branch list.
     *
     * @return the branch mutable list.
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

    public int getBranchCount() {
        return (branches != null) ? branches.size() : 0;
    }

    /*
     * Return the branch at the specified index in this node's "virtual" branch array. @param index
     * an index for a branch. @return the branch with the given index. @exception
     * ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Branch getBranchAt(int index) {
        if (branches != null) {
            return branches.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public boolean isDefinedScope() {
        return name2type != UNDEFINED_SCOPE;
    }

    @SuppressWarnings("unchecked")
    public void setDefinedScope(boolean defined) {
        if (!defined) {
            name2type = UNDEFINED_SCOPE;
            name2var = UNDEFINED_SCOPE;
        } else if (name2type == UNDEFINED_SCOPE) {
            name2type = null;
            name2var = null;
        }
    }

    public List<TypeDeclaration> getTypesInScope() {
        if (name2type == null || name2type.isEmpty()) {
            return new ArrayList<>(0);
        }
        List<TypeDeclaration> res = new ArrayList<>();
        for (TypeDeclaration td : name2type.values()) {
            res.add(td);
        }
        return res;
    }

    public ClassType getTypeInScope(String name) {
        Debug.assertNonnull(name);
        if (name2type == null) {
            return null;
        }
        return name2type.get(name);
    }

    public void addTypeToScope(ClassType type, String name) {
        Debug.assertNonnull(type, name);
        if (name2type == null || name2type == UNDEFINED_SCOPE) {
            name2type = new HashMap<>();
        }
        name2type.put(name, (TypeDeclaration) type);
    }

    public void removeTypeFromScope(String name) {
        Debug.assertNonnull(name);
        if (name2type == null || name2type == UNDEFINED_SCOPE) {
            return;
        }
        name2type.remove(name);
    }

    public List<VariableSpecification> getVariablesInScope() {
        if (name2var == null || name2var.isEmpty()) {
            // TODO EMPTY_LIST ?
            return new ArrayList<>(0);
        }
        List<VariableSpecification> res = new ArrayList<>();
        for (VariableSpecification vs : name2var.values()) {
            res.add(vs);
        }
        return res;
    }

    public VariableSpecification getVariableInScope(String name) {
        Debug.assertNonnull(name);
        if (name2var == null) {
            return null;
        }
        return name2var.get(name);
    }

    public void addVariableToScope(VariableSpecification var) {
        Debug.assertNonnull(var);
        if (name2var == null || name2var == UNDEFINED_SCOPE) {
            name2var = new HashMap<>();
        }
        name2var.put(var.getName(), var);
    }

    public void removeVariableFromScope(String name) {
        Debug.assertNonnull(name);
        if (name2var == null || name2var == UNDEFINED_SCOPE) {
            return;
        }
        name2var.remove(name);
    }

    public void accept(SourceVisitor v) {
        v.visitSwitch(this);
    }

    public SourceElement getLastElement() {
        if (getBranchCount() == 0) {
            return this;
        }
        return getBranchAt(getBranchCount() - 1).getLastElement();
    }
}
