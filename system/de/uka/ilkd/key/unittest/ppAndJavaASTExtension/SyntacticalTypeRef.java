// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.ppAndJavaASTExtension;

import java.io.StringWriter;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReferenceImp;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.util.ExtList;

/**
 * This class in analogously implemented to class {@link de.uka.ilkd.key.java.reference.TypeRef}
 * but it does not support {@code KeYJavaType}s but only {@code Type}s. Its purpose
 * is only for syntactical representation in the java AST in order to be printable
 * by the {@link CompilableJavaPP}. The objective of its independence from 
 * {@code KeYJavaType}s to prevent objects of this class to escape in other parts 
 * of the system like, e.g. {@code JavaInfo}. See Bug #911.
 * @author gladisch
 */
public class SyntacticalTypeRef extends TypeReferenceImp {

    /**
     * Instead of having a KeYJavaType like {@code TypeRef} here we have only a Type.
     */
    public Type type;

    public SyntacticalTypeRef(ExtList children, int dim) {
        super(children, dim);
    }
    /**
     * {@link SyntacticalTypeRef} 
     */
    public SyntacticalTypeRef(Type t) {
        super(new ProgramElementName(t.getName()), //Maybe the fullname is required? 
              0, createPackagePrefix(t));
        this.type = t;
        }

    public SyntacticalTypeRef(Type t, int dim) {
        super(new ProgramElementName(t.getName()), //Maybe the fullname is required?
              dim, createPackagePrefix(t));
        this.type = t;
        }
    
    public static PackageReference createPackagePrefix(Type t) {
        PackageReference ref = null;
        String rest = t.getFullName();
        if (rest.indexOf(".")>0) {
            rest = rest.substring(0, rest.lastIndexOf(".")+1);
            while (rest.indexOf(".")>0) {
            String name = rest.substring(0, rest.indexOf("."));
            rest = rest.substring(rest.indexOf(".")+1);
            ref = new PackageReference(new ProgramElementName(name), ref);
            }
        }
        return ref;
        }
    
    public SyntacticalTypeRef(ProgramElementName name){
        super(name);
    }
            
    public SyntacticalTypeRef(ProgramElementName name, 
            int dimension, 
            ReferencePrefix prefix) {
        super(name, dimension, prefix);
    }
    
    /**If you *effectively* want to call getKeYJavaType().getJavaType() then 
     * just use the {@code type} attribute of this class instead.
     * This method should never be called because SyntacticalTypeRef is supposed
     * to be independent from KeYJavaTypes. This method is declared to overwritte
     * the respective method from the parent class.
     */
    public KeYJavaType getKeYJavaType() {
        throw new RuntimeException("SyntactialTypeRef.getKeYJavaType should never be called.\n" +
        		" If you *effectively* want to call getKeYJavaType().getJavaType() then\n" +
        		" just use the type attribute of this class instead.");
        //return null;
    }

    /**
     * @param p must be an instance of CompilableJavaPP.
     */
    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
	if(!(p instanceof CompilableJavaPP)){
	    CompilableJavaPP cjpp =new CompilableJavaPP(new StringWriter(),false);
	    prettyPrint(cjpp);
	    cjpp.emergencyPrint(p);
	}else{
	    CompilableJavaPP cjpp = (CompilableJavaPP)p;
	    cjpp.printSyntacticalTypeReference(this);
	}
    }

}

