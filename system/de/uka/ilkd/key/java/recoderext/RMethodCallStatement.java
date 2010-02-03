// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.StatementContainer;
import recoder.java.statement.JavaStatement;


public class RMethodCallStatement extends JavaStatement 
    implements StatementContainer, KeYRecoderExtension {


    /** schemavariable needed by meta construct */
    private ProgramVariableSVWrapper resultVar;

    /** schemavariable needed by method call */
    private ExecutionContext ecsvw;

    /**
     *      Body.
     */
    protected Statement body;

        
    /**
     *      Labeled statement.
     *      @param resultVar the ProgramVariable the return value is assigned to
     *      @param ecsvw the ExecutionContext 
     *      @param body a Statement containing the method body of
     *      the called method
     */

    public RMethodCallStatement(ProgramVariableSVWrapper resultVar, 
				ExecutionContext ecsvw,
				Statement body) {
        this.resultVar = resultVar;
	this.ecsvw     = ecsvw;
        this.body      = body;
    }

    /**
     Make parent role valid.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (body != null) {
            body.setStatementContainer(this);
        }
    }

    public int getChildCount() {
        int result = 0;
        if (resultVar != null) result++;
        if (ecsvw != null) result++;
        if (body != null) result++;
        return result;
    }

    /**
     *      Returns the child at the specified index in this node's "virtual"
     *      child array
     *      @param index an index into this node's "virtual" child array
     *      @return the program element at the given position
     *      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *                 of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (resultVar != null) {
            if (index == 0) return resultVar;
            index--;
        }
        if (ecsvw != null) {
            if (index == 0) return ecsvw;
            index--;
        }
        if (body != null) {
            if (index == 0) return body;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: resultVar
        // role 1: execution context
        // role 2: body
        if (resultVar == child) {
            return 0;
        }
        if (ecsvw == child) {
	    return 1;
        }
        if (body == child) {
            return 2;
        }
        return -1;
    }

    /**
     *      Get the number of statements in this container.
     *      @return the number of statements.
     */

    public int getStatementCount() {
        return (body != null) ? 1 : 0;
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
        if (body == p) {
            Statement r = (Statement)q;
            body = r;
            if (r != null) {
                r.setStatementContainer(this);
            }
            return true;
        }
        return false;
    }

     /**
      Get child.
      @return the statement.
      */

     public Statement getChild() {
         return body;
     }


     /**
      Get body.
      @return the statement.
      */

     public Statement getBody() {
         return body;
     }

//     /**
//      Set child.
//      @param statement a statement.
//      */

//     public void setChild(Statement statement) {
//         child = statement;
//     }

    /**
     * schemavariable needed by the metaconstruct (needed by method-call)   
     */
    public void setVariableSV(ProgramVariableSVWrapper sv) {
        this.resultVar = sv;
    }


    public ProgramVariableSVWrapper getVariableSV() {
        return resultVar;
    }
    
    public ExecutionContext getExecutionContext() {
	return ecsvw;
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
        if (body != null && index == 0) {
            return body;
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
