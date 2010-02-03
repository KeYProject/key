// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.recoderext;

import recoder.java.*;
import recoder.java.reference.*;
import recoder.java.statement.JavaStatement;
import recoder.list.generic.*;


/**
 *  A shortcut-statement for a method body.
 */
public class MethodBodyStatement extends JavaStatement implements
    TypeReferenceContainer, ExpressionContainer, NamedProgramElement, ReferenceSuffix {
    
    /**
     * the ast parent
     */
    private StatementContainer astParent;

    protected TypeReference bodySource;
    protected Expression resultVar;    

    private Identifier methodName;
    private ReferencePrefix methodReferencePrefix;
    private ASTList<Expression> arguments;
    private Identifier scope;
    
    /**
     *      Construct a method body shortcut
     *      @param bodySource exact class where the body is declared
     *      @param resultVar the Expression naming the variable to which
     *      the result of the mthod is assigned
     *      @param methRef MethodReference that represents the call
     */
    
    public MethodBodyStatement(TypeReference bodySource, 
			       Expression resultVar,
			       MethodReferenceWrapper methRef) {
        setBodySource(bodySource);
	this.resultVar  = resultVar;        
        setMethodReference(methRef);        
        makeParentRoleValid();        
    }
    


    /**
     *	Set the exact Class the denoted method body is from.
     */
    
    public void setBodySource(TypeReference bodySource) {
	this.bodySource = bodySource;
    }

    /**
     *	Get the exact Class the denoted method body is from.
     *  @returns the TypeReference
     */
    
    public TypeReference getBodySource() {
	return bodySource;
    }


    /**
     *      Set the result variable.
     *      @param resultVar the Expression used as result variable
     */
    
    public void setResultVariable(Expression resultVar) {
	this.resultVar = resultVar;
    }

    /**
     *      Get the result variable.
     *      @return the VariableReference
     */
    
    public Expression getResultVariable() {
	return resultVar;
    }

    /**
     *      Set the MethodReference that caused this call.
     */
    public void setMethodReference(MethodReferenceWrapper methRef) {	
        this.methodName = methRef.getIdentifier();
        this.methodReferencePrefix = methRef.getReferencePrefix();
        this.arguments = methRef.getArguments();
        this.scope = methRef.getScope();
    }

    public NonTerminalProgramElement getASTParent() {
	return astParent;
    }
    
    public Identifier getScope(){
        return scope;
    }

    public StatementContainer getStatementContainer() {
	return astParent;
    }

    public void setStatementContainer(StatementContainer parent) {
	astParent = parent;
    }

    /**
     *      Finds the source element that occurs first in the source.
     *      @return the last source element in the syntactical representation of
     *      this element, may be equals to this element.
     */
    
    public SourceElement getFirstElement() {
        return getChildAt(0).getFirstElement();
    }

    /**
     *      Finds the source element that occurs last in the source.
     *      @return the last source element in the syntactical representation of
     *      this element, may be equals to this element.
     */
    
    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
    }

    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    
    public int getChildCount() {
        int result = 0;
        if (bodySource != null) result++;
        if (resultVar != null) result++;
        if (methodReferencePrefix != null) result++;
        if (methodName != null) result++;
        if (arguments != null) result += arguments.size();
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
        if (bodySource != null) {
            if (index == 0) return bodySource;
            index--;
        }
        if (resultVar != null) {
            if (index == 0) return resultVar;
            index--;
        }
        if (methodReferencePrefix != null) {
            if (index == 0) return methodReferencePrefix;
            index--;
        }
        if (methodName != null) {
            if (index == 0) return methodName;
            index--;
        }
        if (arguments != null) {
            return arguments.get(index);            
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of type references in this container.
     *      @return the number of statements.
     */

    public int getTypeReferenceCount() {
        return (bodySource != null) ? 1 : 0;
    }

    /**
     *       Return the type reference at the specified index in this node's
     *       "virtual" statement array.
     *       @param index an index for a type reference.
     *       @return the type reference with the given index.
     *       @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *       of bounds.
     */

    public TypeReference getTypeReferenceAt(int index) {
        if (bodySource != null && index == 0) {
            return bodySource;
        }
        throw new ArrayIndexOutOfBoundsException();
    }
    

    /**
     *      Get the number of expressions in this container.
     *      @return the number of expressions.
     */

    public int getExpressionCount() {
        int result = 0;
        if (resultVar != null) {
            result++;
        }               
        if (arguments != null) {
            result += arguments.size();
        }
        return result;
    }

    /**
     *       Return the expression at the specified index in this node's
     *       "virtual" expression array.
     *       @param index an index for a expression.
     *       @return the expression with the given index.
     *       @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *       of bounds.
     */
    public Expression getExpressionAt(int index) {
        if (resultVar != null) {
            if (index == 0) return resultVar;
            index--;
        }        
        if (arguments != null) {
            return arguments.get(index);
        }	              
        throw new ArrayIndexOutOfBoundsException();
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
        if (p == null) throw new NullPointerException();
        if (bodySource == p) {
            TypeReference r = (TypeReference)q;
            bodySource = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        else if (resultVar == p) {
            Expression r = (Expression)q;
            resultVar = r;
            if (r != null) {
                r.setExpressionContainer(this);
            }
            return true;
        } else if (methodReferencePrefix == p) {            
            ReferencePrefix rp = (ReferencePrefix) q;
            methodReferencePrefix = rp;
            return true;
        } else if (methodName == p) {
            Identifier id = (Identifier)q;
            methodName = id;            
            return true;
        } else {                               
            for (int i = 0; i < arguments.size(); i++) {
                if (arguments.get(i) == p) {
                    if (q == null) {
                        arguments.remove(i);
                    } else {
                        Expression r = (Expression)q;
                        arguments.set(i, r);
                        r.setExpressionContainer(this);
                    }
                    return true;
                }
            }
        }
        
        return false;
    }

    
    /**
     *      Ensures that each child has "this" as syntactical parent.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();

        if (bodySource != null) {
            bodySource.setParent(this);
        }

        if (resultVar != null) {
            resultVar.setExpressionContainer(this);
        }
        
        if (methodName != null) {
            methodName.setParent(this);
        }
        
        if (methodReferencePrefix != null) {
            methodReferencePrefix.setReferenceSuffix(this);
        }
        
        if (arguments != null) {
            for (int i = 0, sz = arguments.size(); i<sz; i++) {                
                arguments.get(i).setExpressionContainer(this);                
            }
        }
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: bodySource
	// role 1: resultVar
        // role 2: prefix
        // others: arguments
        if (bodySource == child) {
            return 0;
        }
	if (resultVar == child) {
	    return 1;
        }
        if (methodReferencePrefix == child) {
            return 2;
        }
        if (methodName == child) {
            return 3;
        }
        
        for (int i = 0, sz = arguments.size(); i<sz; i++) {                
            final Expression e = arguments.get(i);
            if (e == child) {                
                return i+4;
            }                
        }   
        
        return -1;
    }

    //don't think we need it
    public void accept(SourceVisitor v) {
	throw new IllegalStateException("Not implemented in "
					+"MethodBodyStatement");
    }

    //don't think we need it
    public MethodBodyStatement deepClone() {
	throw new IllegalStateException("Not implemented in "
					+"MethodBodyStatement");
    }    

      
    public String getName() {
        StringBuffer args = new StringBuffer();
        if (arguments != null) {
            for (int i=0; i<arguments.size(); i++) {
                args.append(arguments.get(i));            
                if (i!=arguments.size()-1) {
                    args.append(", ");
                }
            }
        }
        return getBodySource().getName()+"::"+
            getReferencePrefix() + "." + 
            getIdentifier().getText()+"("+args+"):"+resultVar;
    }


    public ASTList<Expression> getArguments() {
        return arguments;
    }


    public void setArguments(ASTList<Expression> arguments) {
        this.arguments = arguments;
    }


    public Identifier getMethodName() {
        return methodName;
    }


    public void setMethodName(Identifier methodName) {
        this.methodName = methodName;
    }


    public ReferencePrefix getMethodReferencePrefix() {
        return methodReferencePrefix;
    }


    public void setMethodReferencePrefix(ReferencePrefix methodReferencePrefix) {
        this.methodReferencePrefix = methodReferencePrefix;
    }


    public Identifier getIdentifier() {        
        return methodName;
    }


    public void setIdentifier(Identifier name) {
        this.methodName = name;        
    }

    public MethodReference getsMethodReference() {        
        return new MethodReference(methodReferencePrefix, methodName, arguments);
    }

    public ReferencePrefix getReferencePrefix() {       
        return methodReferencePrefix;
    }
    
}
