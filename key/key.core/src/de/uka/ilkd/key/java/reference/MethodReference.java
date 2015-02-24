// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.ExpressionStatement;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Method reference.
 *  @author <TT>AutoDoc</TT>
 */
public class MethodReference extends JavaNonTerminalProgramElement
                             implements MethodOrConstructorReference,
                             MemberReference, ReferencePrefix, 
                             ReferenceSuffix, ExpressionStatement, 
                             TypeReferenceContainer, NameReference {
 
    /**
       Access path.
    */
    protected final ReferencePrefix prefix;
    
    /**
     *      Name.
     */
    protected final MethodName name;
    
    /**
     *      Arguments.
     */
    protected final ImmutableArray<? extends Expression> arguments;
    
    public MethodReference(ExtList args, MethodName n, 
                   ReferencePrefix p, PositionInfo pos) {
        super(pos);
        this.prefix = p;
        name = n;
        Debug.assertTrue(name != null, "Tried to reference unnamed method.");
        this.arguments = new ImmutableArray<Expression>(args.collect(Expression.class));       
    }
    
    public MethodReference(ImmutableArray<? extends Expression> args, MethodName n, 
            ReferencePrefix p) {
        this.prefix = p;
        name = n;
        Debug.assertTrue(name != null, "Tried to reference unnamed method.");
        this.arguments = args;        
	checkArguments();
    }
    
    public MethodReference(ImmutableArray<Expression> args, MethodName n, 
			   ReferencePrefix p, PositionInfo pos) {
	super(pos);
	this.prefix=p;
	name = n;
	Debug.assertTrue(name != null, "Tried to reference unnamed method.");
	this.arguments=args;        
	checkArguments();
    }

   public MethodReference(ExtList children, MethodName n, ReferencePrefix p) {
	this(new ImmutableArray<Expression>(children.collect(Expression.class)),
	     n, p, children.get(PositionInfo.class));
    }

     public MethodReference(ExtList children, MethodName n, ReferencePrefix p,PositionInfo pos, String scope) {
	this(new ImmutableArray<Expression>(children.collect(Expression.class)),
	     n, p, pos);
    }

    protected void checkArguments(){
	ImmutableArray<? extends Expression> args = getArguments();
	for(Expression arg:args){
	    if(arg==null) 
		throw new NullPointerException();
	}
    }
    
    public SourceElement getFirstElement() {
        return (prefix == null) ? getChildAt(0).getFirstElement() : prefix.getFirstElement();
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
        return (prefix == null) ? getChildAt(0).getFirstElement() : prefix.getFirstElementIncludingBlocks();
    }


    /**
     *      Get reference prefix.
     *      @return the reference prefix.
     */
    @Override
    public ReferencePrefix getReferencePrefix() {
        return prefix;
    }
    
    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (prefix     != null) result++;
        if (name       != null) result++;
        if (arguments  != null) result += arguments.size();
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
        if (prefix != null) {
            if (index == 0) return prefix;
            index--;
        }
        if (name != null) {
            if (index == 0) return name;
            index--;
        }
        if (arguments != null) {
	    return arguments.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of type references in this container.
     *      @return the number of type references.
     */
    public int getTypeReferenceCount() {
        return (prefix instanceof TypeReference) ? 1 : 0;
    }
    
    

    /*
      Return the type reference at the specified index in this node's
      "virtual" type reference array.
      @param index an index for a type reference.
      @return the type reference with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public TypeReference getTypeReferenceAt(int index) {
        if (prefix instanceof TypeReference && index == 0) {
            return (TypeReference)prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    /**
     *      Get the number of expressions in this container.
     *      @return the number of expressions.
     */
    public int getExpressionCount() {
        int result = 0;
        if (prefix instanceof Expression) result += 1;
        if (arguments != null) {
            result += arguments.size();
        }
        return result;
    }

    /*
      Return the expression at the specified index in this node's
      "virtual" expression array.
      @param index an index for an expression.
      @return the expression with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public Expression getExpressionAt(int index) {
        if (prefix instanceof Expression) {
            if (index == 0) {
                return (Expression)prefix;
            }
            index -= 1;
        }
        if (arguments != null) {
            return arguments.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get name.
     *      @return the string.
     */
    public final String getName() {
        return (name == null) ? null : name.toString();
    }

    /**
     *      Get identifier.
     *      @return the identifier.
     */
    public ProgramElementName getProgramElementName() {
	if (name instanceof ProgramElementName) {
	    return (ProgramElementName) name; 	
	} else if (name instanceof SchemaVariable) {
	    return (((ProgramSV)name).getProgramElementName());
	} else return null;
    }

    /**
     *      Get arguments.
     *      @return the expression array wrapper.
     */
    @Override
    public ImmutableArray<? extends Expression> getArguments() {
        return arguments;
    }

    /**
     *      Gets index-th argument    
     *      @return the expression 
     */
    public Expression getArgumentAt(int index) {
        if (arguments != null) {
            return arguments.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * determines the arguments types and constructs a signature of the current
     * method
     */
    public ImmutableList<KeYJavaType> getMethodSignature(Services services,
						ExecutionContext ec) {
	ImmutableList<KeYJavaType> signature = ImmutableSLList.<KeYJavaType>nil();
	if (arguments != null) {
            final TypeConverter typeConverter = services.getTypeConverter();
	    for (int i = arguments.size()-1; i>=0; i--) {		
                signature = signature.prepend
                    (typeConverter.getKeYJavaType(getArgumentAt(i), ec));
	    }
	}
	return signature;
    }
    
    /**
     * returns the static KeYJavaType of the methods prefix
     */
    public KeYJavaType determineStaticPrefixType(Services services, 
                                                 ExecutionContext ec) {
	KeYJavaType prefixType;
        if (prefix == null) {
	    prefixType = ec.getTypeReference().getKeYJavaType();
	} else {
	    if (prefix instanceof Expression) {
	        prefixType = ((Expression)prefix).getKeYJavaType(services, ec);
	    } else {
	        prefixType = ((TypeReference)prefix).getKeYJavaType();
	    }
	}
        return prefixType;        
    }
    
    public IProgramMethod method(Services services, 
            			KeYJavaType refPrefixType, 
            			ExecutionContext ec) {	
        ProgramVariable inst = services.getJavaInfo().getAttribute(
                ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, ec.getTypeReference().getKeYJavaType());
        IProgramMethod pm = method(services, refPrefixType, 
                getMethodSignature(services, ec),
                ec.getTypeReference().getKeYJavaType());
        while(inst!=null && pm==null){
            KeYJavaType classType = inst.getKeYJavaType();
            pm = method(services, classType, 
                    getMethodSignature(services, ec),
                    classType);
            if(pm!=null){
                return pm;
            }
            inst = services.getJavaInfo().getAttribute(
                    ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, classType);
        }
        return pm;
    }
    
    /**
     * 
     * @param services the Services class offering access to metamodel 
     * information
     * @param classType the KeYJavaType where to start looking for the 
     * declared method
     * @param signature the IList<KeYJavaType> of the arguments types
     * @param context the KeYJavaType from where the method is called  
     * @return the found program method
     */
    public IProgramMethod method
    	(Services services, KeYJavaType classType, 
    	        ImmutableList<KeYJavaType> signature, 
    	        KeYJavaType context) {
        final String methodName = name.toString();        
        IProgramMethod pm = services.getJavaInfo().getProgramMethod(classType, 
                methodName, signature, context);
	return pm;
    }
    
    public boolean implicit() {
	return getProgramElementName().toString().charAt(0)=='<';
    }

    public MethodName getMethodName() {
	return name;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnMethodReference(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printMethodReference(this);
    }

    public KeYJavaType getKeYJavaType(Services services, 
				      ExecutionContext ec) {
	IProgramMethod meth = method(services, 
	        determineStaticPrefixType(services, ec), ec);
	if(meth == null){
	    return ec.getTypeReference().getKeYJavaType();
	}
	return meth.getReturnType();
		      
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {	
	return getKeYJavaType();
    }

    public KeYJavaType getKeYJavaType() {
	Debug.fail("");
	return null;
    }

}