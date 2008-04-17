// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.java.recoderext;

import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.CompilationUnit;
import recoder.java.Identifier;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.DeclarationSpecifier;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.modifier.Public;
import recoder.java.reference.FieldReference;
import recoder.java.reference.PackageReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.java.statement.Return;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 */
public class JVMIsTransientMethodBuilder extends RecoderModelTransformer {

    public static final String 
	IMPLICIT_JVM_IS_TRANSIENT = "<jvmIsTransient>";

    public static final String 
	IMPLICIT_TRANSACTION_COUNTER  = "<transactionCounter>";

    private boolean alreadyTransformed = false;

    public JVMIsTransientMethodBuilder
	(CrossReferenceServiceConfiguration services, 
	 TransformerCache cache) {	
	super(services, cache);
    }

    private ReferencePrefix createJavaLangPrefix() {
	return new PackageReference
	    (new PackageReference(new Identifier("java")),
	     new Identifier("lang"));
    }

    /**
     * creates the implicit  <code>&lt;jvmIsTransient&gt(Object obj);</code>
     * method 
     * @param type the TypeDeclaration 
     * @return the implicit method
     */
    public MethodDeclaration createMethod(ClassDeclaration type) {	
	ParameterDeclaration paramDecl = new ParameterDeclaration
	    (new TypeReference(createJavaLangPrefix(), 
			       new Identifier("Object")), 
	     new Identifier("obj"));

	ASTList<Statement> body = new ASTArrayList<Statement>(2);
	
	body.add(new Return
		 (new FieldReference
		  (new VariableReference(new Identifier("obj")),
		   new ImplicitIdentifier
		   (ImplicitFieldAdder.IMPLICIT_TRANSIENT))));

	ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<DeclarationSpecifier>(2);
	modifiers.add(new Public());

	ASTList<ParameterDeclaration> params = 
	    new ASTArrayList<ParameterDeclaration>(1);
	params.add(paramDecl);

	MethodDeclaration md = new MethodDeclaration
	    (modifiers, 
	     new TypeReference(new Identifier("int")), 
	     new ImplicitIdentifier(IMPLICIT_JVM_IS_TRANSIENT),
	     params, null, new StatementBlock(body));

	md.makeAllParentRolesValid();
	return md;
    }    


    /**
     * entry method for the constructor normalform builder
     * @param td the TypeDeclaration 
     */
    protected void makeExplicit(TypeDeclaration td) {
	if (alreadyTransformed) return;
	if ("KeYJCSystem".equals(td.getName())) {

	    PackageReference pr = 
		td.getASTParent() instanceof CompilationUnit ? 
		((CompilationUnit)td.getASTParent()).
		getPackageSpecification().getPackageReference() : null;
	    String[] keyJavaCard = { "de", "uka", "ilkd", "key", "javacard" };
	    PackageReference prefix = pr;
	    boolean res = true;
	    for(int i=keyJavaCard.length-1; i>=0; i--) {
		if(prefix == null || !keyJavaCard[i].equals(prefix.getName())){
		  res = false;
		  break;
		}
		prefix = (PackageReference)prefix.getReferencePrefix();
	    }
            if(res) {
		    attach(ImplicitFieldAdder.createImplicitRecoderField
			   ("int", IMPLICIT_TRANSACTION_COUNTER, true, true), td, 0);
		    attach(createMethod((ClassDeclaration)td), td, 
                            td.getMembers().size());
		    alreadyTransformed = true;
            }
	}
    }






}
