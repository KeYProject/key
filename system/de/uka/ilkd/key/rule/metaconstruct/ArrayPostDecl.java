// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.ArrayOfModifier;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ArrayPostDecl extends ProgramMetaConstruct {

    public ArrayPostDecl(SchemaVariable sv) {
	super(new Name("array-post-declaration"), (ProgramSV)sv);
    }


    /** 
     * Replaces a local variable declaration <code> #t #v[]; </code> with
     * <code>#t[] #v;</code>
     * @param services the Services with all necessary information 
     * about the java programs
     * @param svInst the instantiations of the schema variables
     * @return the transformed program
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
					    Services services,
					    SVInstantiations svInst) {


	final LocalVariableDeclaration declaration = (LocalVariableDeclaration)pe;
	final ArrayOfModifier modifiers = declaration.getModifiers();
	final TypeReference originalTypeReference = declaration.getTypeReference();
	/*	Debug.assertTrue
	    (declaration.getVariables().size() == 1,
	    "ArrayPostDecl metaconsstruct can only treat single variable declarations");*/
	final VariableSpecification var = 
	    declaration.getVariables().getVariableSpecification(0);
	
	final TypeReference newTypeReference = 
	    new TypeRef(originalTypeReference.getProgramElementName(),
			originalTypeReference.getDimensions() + var.getDimensions(),
			originalTypeReference.getReferencePrefix(),
			var.getProgramVariable().getKeYJavaType());

	final VariableSpecification newVar = new VariableSpecification
	    (var.getProgramVariable(), 0, var.getInitializer(), var.getType());

	return new LocalVariableDeclaration(modifiers, 
					    newTypeReference, 
					    newVar);

    }

}
