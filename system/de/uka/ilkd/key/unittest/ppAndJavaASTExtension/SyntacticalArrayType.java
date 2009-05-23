package de.uka.ilkd.key.unittest.ppAndJavaASTExtension;

import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.ProgramElementName;

public class SyntacticalArrayType implements ArrayType {
    ProgramElementName baseName;
    int dim;
    String prefix;
    SyntacticalTypeRef syntr;
    
    public SyntacticalArrayType(String prefix, ProgramElementName name, int dimension){
	baseName=name;
	this.dim = dimension;
	this.prefix = prefix;
	syntr= new SyntacticalTypeRef(this);
    }

    public SyntacticalArrayType(String prefix, String name, int arity){
	this(prefix,new ProgramElementName(name),arity);
    }

    public String getAlternativeNameRepresentation() {
	return getFullName();
    }

    public TypeReference getBaseType() {
	return syntr;
    }

    public int getDimension() {
	// TODO Auto-generated method stub
	return dim;
    }

    public String getFullName() {
	if(prefix!=null){
	    return prefix+"."+getName();
	}else{
	    return getName();
	}
    }

    public String getName() {
	String tmp =baseName.getProgramName();
	for(int i=0;i<dim;i++){
	    tmp+="[]";
	}
	return tmp;
    }

    public Literal getDefaultValue() {
	// TODO Auto-generated method stub
	return null;
    }

}
