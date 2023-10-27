/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.*;
import recoder.java.expression.ArrayInitializer;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

/**
 * The array allocation operator. There are two variants for NewArray:
 * <OL>
 * <LI>Ordinary array construction <BR>
 * <tt>new XYZ[d<sub>1</sub>]...[d<sub>n</sub>]</tt>
 * <LI>Initialized array construction <BR>
 * <tt>new XYZ[]...[] { a<sub>1</sub>, ..., a<sub>n</sub> }
 * </OL>
 * Contrary to an ordinary New, a NewArray is no ConstructorReference (since all ArrayType
 * constructors are predefined) and is not used as a Statement (since there are no sideeffects in
 * the constructor). No access path is required for new, since there is no inner class problem.
 * <p>
 * NewArray has either a list of dimension length expressions, or a single ArrayInitializer.
 */

public class NewArray extends TypeOperator implements Reference, ReferencePrefix {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 836360320945022449L;

    /**
     * Dimensions.
     */

    protected int dimensions;

    /**
     * Array initializer.
     */

    protected ArrayInitializer arrayInitializer;

    /**
     * Reference parent.
     */

    protected ReferenceSuffix referenceParent;

    /**
     * New array.
     */

    public NewArray() {
        // nothing to do
    }

    /**
     * New array.
     *
     * @param arrayName a type reference.
     * @param dimExpr an expression mutable list.
     */

    public NewArray(TypeReference arrayName, ASTList<Expression> dimExpr) {
        setTypeReference(arrayName);
        setArguments(dimExpr);
        makeParentRoleValid();
    }

    /**
     * New array.
     *
     * @param arrayName a type reference.
     * @param dimensions an int value.
     * @param initializer an array initializer.
     */

    public NewArray(TypeReference arrayName, int dimensions, ArrayInitializer initializer) {
        setTypeReference(arrayName);
        setDimensions(dimensions);
        setArrayInitializer(initializer);
        makeParentRoleValid();
    }

    /**
     * New array.
     *
     * @param proto a new array.
     */

    protected NewArray(NewArray proto) {
        super(proto);
        if (proto.arrayInitializer != null) {
            arrayInitializer = proto.arrayInitializer.deepClone();
        }
        dimensions = proto.dimensions;
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public NewArray deepClone() {
        return new NewArray(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (arrayInitializer != null) {
            arrayInitializer.setExpressionContainer(this);
        }
    }

    public SourceElement getLastElement() {
        if (arrayInitializer != null) {
            return arrayInitializer.getLastElement();
        }
        return this;
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 (IDX): subexpression, or parameters
        // role 1: type reference (for type operators only)
        // role 2: prefix (for New only)
        // role 3: class declaration (for New only), or
        // array initializer (for NewArray)
        if (children != null) {
            int index = children.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 0;
            }
        }
        if (typeReference == child) {
            return 1;
        }
        if (arrayInitializer == child) {
            return 3;
        }
        return -1;
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        if (expressionParent != null) {
            return expressionParent;
        } else {
            return referenceParent;
        }
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 0;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 0;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return PREFIX;
    }

    /**
     * Get reference suffix.
     *
     * @return the reference suffix.
     */

    public ReferenceSuffix getReferenceSuffix() {
        return referenceParent;
    }

    /**
     * Set reference suffix.
     *
     * @param path a reference suffix.
     */

    public void setReferenceSuffix(ReferenceSuffix path) {
        referenceParent = path;
    }

    /**
     * Get expression container.
     *
     * @return the expression container.
     */

    public ExpressionContainer getExpressionContainer() {
        return expressionParent;
    }

    /**
     * Set expression container.
     *
     * @param parent an expression container.
     */

    public void setExpressionContainer(ExpressionContainer parent) {
        expressionParent = parent;
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
     * dim must be >= getDimensionLengths().size() If not, the dimensions are ignored during pretty
     * print, but the model is not considered valid!
     */

    public void setDimensions(int dim) {
        dimensions = dim;
    }

    /**
     * Get array initializer.
     *
     * @return the array initializer.
     */

    public ArrayInitializer getArrayInitializer() {
        return arrayInitializer;
    }

    /**
     * Set array initializer.
     *
     * @param init an array initializer.
     */

    public void setArrayInitializer(ArrayInitializer init) {
        arrayInitializer = init;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (typeReference != null) {
            result++;
        }
        if (children != null) {
            result += children.size();
        }
        if (arrayInitializer != null) {
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
        int len;
        if (typeReference != null) {
            if (index == 0) {
                return typeReference;
            }
            index--;
        }
        if (children != null) {
            len = children.size();
            if (len > index) {
                return children.get(index);
            }
            index -= len;
        }
        if (arrayInitializer != null) {
            if (index == 0) {
                return arrayInitializer;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    public int getExpressionCount() {
        int result = 0;
        if (children != null) {
            result += children.size();
        }
        if (arrayInitializer != null) {
            result++;
        }
        return result;
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression
     * array. @param index an index for an expression. @return the expression with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Expression getExpressionAt(int index) {
        int len;
        if (children != null) {
            len = children.size();
            if (len > index) {
                return children.get(index);
            }
            index -= len;
        }
        if (arrayInitializer != null) {
            if (index == 0) {
                return arrayInitializer;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
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
        count = (children == null) ? 0 : children.size();
        for (int i = 0; i < count; i++) {
            if (children.get(i) == p) {
                if (q == null) {
                    children.remove(i);
                } else {
                    Expression r = (Expression) q;
                    children.set(i, r);
                    r.setExpressionContainer(this);
                }
                return true;
            }
        }
        if (typeReference == p) {
            TypeReference r = (TypeReference) q;
            typeReference = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        if (arrayInitializer == p) {
            ArrayInitializer r = (ArrayInitializer) q;
            arrayInitializer = r;
            if (r != null) {
                r.setExpressionContainer(this);
            }
            return true;
        }
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitNewArray(this);
    }
}
