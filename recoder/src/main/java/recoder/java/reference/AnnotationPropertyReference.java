/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;
import recoder.java.declaration.AnnotationElementValuePair;

/**
 * @author ich
 */
public class AnnotationPropertyReference extends JavaNonTerminalProgramElement
        implements MemberReference {
    /**
     * serialization id
     */
    private static final long serialVersionUID = 5822661522219760793L;

    protected Identifier ident;

    protected AnnotationElementValuePair parent;

    public AnnotationPropertyReference() {
        super();
    }

    public AnnotationPropertyReference(Identifier ident) {
        super();
        this.ident = ident;
        makeParentRoleValid();
    }

    public AnnotationPropertyReference(AnnotationPropertyReference proto) {
        super(proto);
        this.ident = proto.ident.deepClone();
        makeParentRoleValid();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.ProgramElement#getASTParent()
     */
    public NonTerminalProgramElement getASTParent() {
        return parent;
    }

    public AnnotationElementValuePair getParent() {
        return parent;
    }

    public void setParent(AnnotationElementValuePair parent) {
        this.parent = parent;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#accept(recoder.java.SourceVisitor)
     */
    public void accept(SourceVisitor v) {
        v.visitAnnotationPropertyReference(this);

    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#deepClone()
     */
    public AnnotationPropertyReference deepClone() {
        return new AnnotationPropertyReference(this);
    }

    public int getChildCount() {
        return ident == null ? 0 : 1;
    }

    public ProgramElement getChildAt(int index) {
        if (ident != null && index == 0) {
            return ident;
        }
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public int getChildPositionCode(ProgramElement child) {
        // 0: identifier
        return child == ident ? 0 : -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == ident) {
            ident = (Identifier) q;
            if (ident != null) {
                ident.setParent(this);
            }
            return true;
        }
        return false;
    }

    public Identifier getIdentifier() {
        return ident;
    }

    public void setIdentifier(Identifier ident) {
        this.ident = ident;
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (ident != null) {
            ident.setParent(this);
        }
    }

    public int getExpressionCount() {
        return 0;
    }

    public Expression getExpressionAt(@SuppressWarnings("unused") int index) {
        throw new IndexOutOfBoundsException();
    }

    public SourceElement getFirstElement() {
        return ident;
    }

    public SourceElement getLastElement() {
        return ident;
    }

}
