// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


// This file is taken from the RECODER library, which is protected by the LGPL,
// and modified.
/** This class is part of the AST RECODER builds when it parses and resolves Java
 * programs with meta constructs and schema variables. It is transformed by Recoder2KeY
 * to a subclass of ...rule.metaconstruct.ProgramMetaConstruct.
 */

package de.uka.ilkd.key.java.recoderext;

import recoder.java.*;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.java.statement.JavaStatement;
import recoder.list.generic.ASTList;


public class RMethodBodyStatement extends JavaStatement 
    implements KeYRecoderExtension, TypeReferenceContainer, 
    ExpressionContainer, NamedProgramElement {

    /**
     * 
     */
    private static final long serialVersionUID = -8427953809480454933L;
    private TypeReference bodySource; 
    private ProgramVariableSVWrapper resultVar;
    
    private ReferencePrefix methodReferencePrefix;
    private Identifier methodName;    
    private ASTList<Expression> arguments;

    public RMethodBodyStatement(TypeReference typeRef, 
                                ProgramVariableSVWrapper resVar, 
                                MethodReference mr) {
        this.bodySource = typeRef;
        this.resultVar = resVar;
        setMethodReference(mr);
        makeParentRoleValid();
    }

    public RMethodBodyStatement(TypeReference typeRef, 
            ProgramVariableSVWrapper resVar, 
            ReferencePrefix prefix, Identifier methodName, 
            ASTList<Expression> arguments) {
        this.bodySource = typeRef;
        this.resultVar = resVar;
        this.methodReferencePrefix = prefix;
        this.methodName = methodName;
        this.arguments = arguments;
        makeParentRoleValid();
    }

    

    public void accept(SourceVisitor visitor) {
    }

    public RMethodBodyStatement deepClone() {
        return new RMethodBodyStatement
            (bodySource.deepClone(), 
             (ProgramVariableSVWrapper)resultVar.deepClone(), 
             (ReferencePrefix)methodReferencePrefix.deepClone(),
             methodName.deepClone(),
             arguments.deepClone());
    }
    
    /**
     *      Set the MethodReference that caused this call.
     */
    public void setMethodReference(MethodReference methRef) {   
        this.methodName = methRef.getIdentifier();
        this.methodReferencePrefix = methRef.getReferencePrefix();
        this.arguments = methRef.getArguments();
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

    
    /**
     *      Ensures that each child has "this" as syntactical parent.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();

        if (bodySource != null) {
            bodySource.setParent(this);
        }

        if (resultVar != null) {
            resultVar.setParent(this);
        }
        
        if (methodName != null) {
            methodName.setParent(this);
        }
        
        if (arguments != null) {
            for (int i = 0, sz = arguments.size(); i<sz; i++) {                
                arguments.get(i).setExpressionContainer(this);                
            }
        }
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
            ProgramVariableSVWrapper r = (ProgramVariableSVWrapper)q;
            resultVar = r;
            if (r != null) {
                r.setParent(this);
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
            for (int i = 0, sz = arguments.size(); i<sz; i++) {                
                final Expression e = arguments.get(i);
                if (e == p) {
                    arguments.set(i, e);
                    e.setExpressionContainer(this);
                    return true;
                }                
            }
            
        }
        
        return false;
    }

    public TypeReference getBodySource() {        
        return bodySource;
    }

    public ProgramVariableSVWrapper getResultVar() {
        return resultVar;
    }

    public MethodReference getMethodReference() {
        return new MethodReference(methodReferencePrefix, methodName, arguments);
    }
    

    public int getTypeReferenceCount() {       
        return bodySource == null ? 0 : 1;
    }

    public TypeReference getTypeReferenceAt(int index) {
        if (bodySource != null && index == 0) {
            return bodySource;
        }
        throw new ArrayIndexOutOfBoundsException();      
    }

    public int getExpressionCount() {        
        return arguments == null ? 0 : arguments.size();
        
    }

    public Expression getExpressionAt(int index) {
        if (arguments != null) {
            return arguments.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public Identifier getIdentifier() {
        return methodName;
    }

    public void setIdentifier(Identifier methodName) {
        this.methodName = methodName; 
        
    }

    public String getName() {      
        return methodName.toString();
    }
}
