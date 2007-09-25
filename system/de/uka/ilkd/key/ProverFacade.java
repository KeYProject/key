// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.VarAndType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.CollectionSort;
import de.uka.ilkd.key.logic.sort.NonCollectionSort;
import de.uka.ilkd.key.logic.sort.Sort;

public interface ProverFacade {

    Sort getSortForClass(String name);
    boolean isSortForClass(Sort s);

    Sort getNumberSort();

    Sort getSortForOCLInteger();
  
        
    Sort getSortForOCLReal();
    Sort getSortForOCLString();
    Sort getSortForOCLBoolean();

    KeYJavaType getKeYJavaTypeForOCLInteger();
    KeYJavaType getKeYJavaTypeForOCLReal();
    KeYJavaType getKeYJavaTypeForOCLString();
    KeYJavaType getKeYJavaTypeForOCLBoolean();

    KeYJavaType getKeYJavaTypeForClass(String name);

    Sort getSortForOCLType();

    Sort getElementSortForCollectionSort(CollectionSort collSort);

    Sort getSortForOCLSet(NonCollectionSort elem);
    Sort getSortForOCLSequence(NonCollectionSort elem);
    Sort getSortForOCLBag(NonCollectionSort elem);

    //    ProgramVariable getProgramVariable(String name,Sort s);
    ProgramVariable getProgramVariable(String name,KeYJavaType s);    
    ProgramVariable getProgramVariable(String name);    

    void doNotAddProgramVariables();

    Function getRigidFunctionForFeature(String attr,Sort[] argSorts,Sort retSort);
    Function getRigidFunctionForStaticFeature (String attr,
                                          Sort enclosingClass,
                                          Sort retSort);
    ProgramMethod getQueryForFeature(String method, Term[] argterms);
    

    JavaBlock getMethodCall(ProgramVariable reference,
			    String method,
			    ProgramVariable result,
			    ProgramVariable[] args);

    JavaBlock getMethodCall(ProgramVariable reference,
			    String method,
			    ProgramVariable result,
			    ProgramVariable[] args,
			    VarAndType[] excProgVars);


    JavaBlock getVoidMethodCall(ProgramVariable reference,
				String method,
				ProgramVariable[] args);

    JavaBlock getVoidMethodCall(ProgramVariable reference,
				String method,
				ProgramVariable[] args,
				VarAndType[] excProgVars);


    JavaBlock getMethodCall(String method,
			    ProgramVariable result,
			    ProgramVariable[] args);

    JavaBlock getVoidMethodCall(String method,
				ProgramVariable[] args);

    JavaBlock getConstructorCall(KeYJavaType cls,
				 ProgramVariable result,
				 ProgramVariable[] args);

    Function getCollectionFunctionForFeature(String attr,
					     Sort[] argSorts,
					     Sort retSort);


    Services services();

    Term getNullTerm();

    ProgramVariable getAttribute(String name, 
				 KeYJavaType classReference);
    
    Term getAttributeTerm(ProgramVariable pvar, Term obj);

    
}




