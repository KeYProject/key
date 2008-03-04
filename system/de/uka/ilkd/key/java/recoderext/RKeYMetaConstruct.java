// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

// This file is taken from the RECODER library, which is protected by the LGPL,
// and modified.
/** This class is part of the AST RECODER builds when it parses and resolves Java
 * programs with meta constructs and schema variables. It is transformed by Recoder2KeY
 * to a subclass of ...rule.metaconstruct.ProgramMetaConstruct.
 */

package de.uka.ilkd.key.java.recoderext;


import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.StatementContainer;
import recoder.java.statement.JavaStatement;
import de.uka.ilkd.key.logic.op.ProgramSV;

public class RKeYMetaConstruct extends JavaStatement 
    implements StatementContainer, KeYRecoderExtension {


    /**
     Child
     */
    protected Statement child=null;
    protected String name="";

    /** schemavariable needed by meta construct */
    private List sv = new Vector(); //of ProgramVariableSVWrapper

    /**
     Loop statement.
     @param proto a loop statement.
     */

    protected RKeYMetaConstruct(RKeYMetaConstruct proto) {
        super(proto);
        if (proto.child != null) {
            child = (Statement)proto.child.deepClone();
        }
    }

    public RKeYMetaConstruct() {
    }

    /**
     Make parent role valid.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (child != null) {
            child.setStatementContainer(this);
        }
    }

    /**
     Returns the number of children of this node.
     @return an int giving the number of children of this node
    */
    public int getChildCount() {
        int result = 0;
        if (child    != null) result++;
        return result;
    }

    /**
     Returns the child at the specified index in this node's "virtual"
     child array
     @param index an index into this node's "virtual" child array
     @return the program element at the given position
     @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
                of bounds
    */
    public ProgramElement getChildAt(int index) {
        if (child != null) {
            if (index == 0) return child;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    public int getChildPositionCode(ProgramElement child0) {
        // role 0: child
        if (child0 == child) {
            return 0;
        }
        return -1;
    }


    /**
     * Replace a single child in the current node.
     * The child to replace is matched by identity and hence must be known
     * exactly. The replacement element can be null - in that case, the child
     * is effectively removed.
     * The parent role of the new child is validated, while the
     * parent link of the replaced child is left untouched.
     * @param p the old child.
     * @param q the new child.
     * @return true if a replacement has occured, false otherwise.
     * @exception ClassCastException if the new child cannot take over
     *            the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (child == p) {
            Statement r = (Statement)q;
            child = r;
            if (r != null) {
                r.setStatementContainer(this);
            }
            return true;
        }
        return false;
    }


    /**
     * sets a String name of this meta construct like 'unwind-loop'
     * @param s the String
     */
    public void setName(String s) {
	name=s;
    }

    /**
     * returns a String name of this meta construct.
     */
    public String getName() {
	return name;
    }


    /**
     Get child.
     @return the statement.
     */

    public Statement getChild() {
        return child;
    }

    /**
     Set child.
     @param statement a statement.
     */

    public void setChild(Statement statement) {
        child = statement;
    }

    /**
     * first schemavariable needed by the metaconstruct
     * @param sv an SVWrapper containing the first Schemavariable
     */

    public void setSV(SVWrapper sv) {
        this.sv.add(0,sv);
    }

    public void addSV(SVWrapper svw) {
	this.sv.add(svw);
    }

    /**
     * first schemavariable needed by the metaconstruct
     * @return first schemavariable needed by the metaconstruct
     */
    public SVWrapper getFirstSV() {
        return (SVWrapper)sv.get(0);
    }

    public ProgramSV[] getSV() {
	ProgramSV[] res = new ProgramSV[sv.size()];
	Iterator it = sv.iterator();
	int i=0;
	while (it.hasNext()) {
	    res[i++]=(ProgramSV)((SVWrapper)it.next()).getSV();
	}
	return res;
    }

    /**
     Get the number of statements in this container.
     @return the number of statements.
     */

    public int getStatementCount() {
        return (child != null) ? 1 : 0;
    }

    /*
      Return the statement at the specified index in this node's
      "virtual" statement array.
      @param index an index for a statement.
      @return the statement with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public Statement getStatementAt(int index) {
        if (child != null && index == 0) {
            return child;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    //don't think we need it
    public void accept(SourceVisitor v) {
    }
    
    //???
    public JavaStatement deepClone() {
	return null;
    }


}
