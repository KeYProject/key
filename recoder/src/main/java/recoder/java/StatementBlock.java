/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import recoder.abstraction.ClassType;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.TypeDeclarationContainer;
import recoder.java.declaration.VariableSpecification;
import recoder.java.statement.JavaStatement;
import recoder.list.generic.ASTList;
import recoder.util.Debug;

/**
 * Statement block.
 *
 * @author AL
 * @author <TT>AutoDoc</TT>
 */

public class StatementBlock extends JavaStatement
        implements StatementContainer, TypeDeclarationContainer, VariableScope, TypeScope {

    /**
     * Undefined scope tag.
     */
    protected final static Map UNDEFINED_SCOPE = new HashMap(1);
    /**
     * serialization id
     */
    private static final long serialVersionUID = -3288497346043639754L;
    /**
     * Body.
     */
    protected ASTList<Statement> body;
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
     * Statement block.
     */
    public StatementBlock() {
        // nothing to do
    }

    /**
     * Statement block.
     *
     * @param block a statement mutable list.
     */
    public StatementBlock(ASTList<Statement> block) {
        setBody(block);
        makeParentRoleValid();
    }

    /**
     * Statement block.
     *
     * @param proto a statement block.
     */

    protected StatementBlock(StatementBlock proto) {
        super(proto);
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

    public StatementBlock deepClone() {
        return new StatementBlock(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (body != null) {
            for (int i = body.size() - 1; i >= 0; i -= 1) {
                body.get(i).setStatementContainer(this);
            }
        }
    }

    /**
     * Get body.
     *
     * @return the statement mutable list.
     */

    public ASTList<Statement> getBody() {
        return body;
    }

    /**
     * Set body.
     *
     * @param list a statement mutable list.
     */

    public void setBody(ASTList<Statement> list) {
        body = list;
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
        if (p == null) {
            throw new NullPointerException();
        }
        int count;
        count = (body == null) ? 0 : body.size();
        for (int i = 0; i < count; i++) {
            if (body.get(i) == p) {
                if (q == null) {
                    body.remove(i);
                } else {
                    Statement r = (Statement) q;
                    body.set(i, r);
                    r.setStatementContainer(this);
                }
                return true;
            }
        }
        return false;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        return (body != null) ? body.size() : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (body != null) {
            int len = body.size();
            if (len > index) {
                return body.get(index);
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 (IDX): statements
        if (body != null) {
            int index = body.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 0;
            }
        }
        return -1;
    }

    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */

    public int getStatementCount() {
        return (body != null) ? body.size() : 0;
    }

    /*
     * Return the statement at the specified index in this node's "virtual" statement array. @param
     * index an index for a statement. @return the statement with the given index. @exception
     * ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Statement getStatementAt(int index) {
        if (body != null) {
            return body.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of type declarations in this container.
     *
     * @return the number of type declarations.
     */

    public int getTypeDeclarationCount() {
        int count = 0;
        if (body != null) {
            for (int i = body.size() - 1; i >= 0; i -= 1) {
                if (body.get(i) instanceof TypeDeclaration) {
                    count += 1;
                }
            }
        }
        return count;
    }

    /*
     * Return the type declaration at the specified index in this node's "virtual" type declaration
     * array. @param index an index for a type declaration. @return the type declaration with the
     * given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (body != null) {
            int s = body.size();
            for (int i = 0; i < s && index >= 0; i += 1) {
                Statement st = body.get(i);
                if (st instanceof TypeDeclaration) {
                    if (index == 0) {
                        return (TypeDeclaration) st;
                    }
                    index -= 1;
                }
            }
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
        } else {
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
            return new ArrayList<>();
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
        v.visitStatementBlock(this);
    }
}
