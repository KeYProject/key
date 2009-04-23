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
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class TypeOf extends ProgramMetaConstruct {
    
     /** creates a typeof ProgramMetaConstruct 
     * @param pe the instance of expression contained by 
     * the meta construct 
     */
    public TypeOf(ProgramElement pe) {
	super("#typeof", pe); 
	
    }

    /** performs the program transformation needed for symbolic
     * program transformation 
     * @return the transformated program
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
					    Services services,
					    SVInstantiations insts) {

	ExecutionContext ec = null;
	
        if (insts.getContextInstantiation() != null) {
	    ec = insts.getContextInstantiation().activeStatementContext();
	}
        KeYJavaType kjt=null;
        if(pe instanceof Expression){
            kjt = services.getTypeConverter().getKeYJavaType((Expression)pe, ec);
        }else{
            kjt = ((TypeRef) pe).getKeYJavaType();
        }
        
        assert kjt != null;  
        
	if (!(kjt.getJavaType() instanceof PrimitiveType)) {
	    if (kjt.getJavaType() instanceof ArrayType) {
		return new TypeRef(kjt, ((ArrayType)kjt.
					 getJavaType()).getDimension());
	    }
	}
        
	

	return new TypeRef(kjt);
    }
}
