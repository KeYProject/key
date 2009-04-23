// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                  Universitaet Koblenz-Landau, Germany
//                  Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SLListOfParsableVariable;


/**
 * Convenience class for creating variables to represent the 
 * elements of an operation's signature.
 * (Creating such variables is necessary in a number of situations,
 * such as when creating or applying an operation contract, or when
 * creating a proof obligation)
 */
public class SignatureVariablesFactory {
    
    public static final SignatureVariablesFactory INSTANCE 
        = new SignatureVariablesFactory();
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    private SignatureVariablesFactory() {
    }
    
    

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    /**
     * Returns an available name constructed by affixing a counter to the passed 
     * base name.
     */
    private ProgramElementName getNewName(Services services, 
                                          String baseName,
                                          boolean makeNameUnique) {
        if(!makeNameUnique) {
            return new ProgramElementName(baseName);
        }
        
        NamespaceSet namespaces = services.getNamespaces();
            
        int i = 0;
        ProgramElementName name;
        do {
            name = new ProgramElementName(baseName + "_" + i++);
        } while(namespaces.lookup(name) != null);
        
        return name;
    }
    

    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Creates a program variable for "self".
     */
    public ProgramVariable createSelfVar(Services services, 
                                         ProgramMethod pm,
                                         boolean makeNameUnique) {
        if(pm.isStatic()) {
            return null;
        } else {
            return new LocationVariable(getNewName(services, 
                                                   "self",
                                                   makeNameUnique), 
                                        pm.getContainerType());
        }
    }
    
    
    /**
     * Creates program variables for the parameters.
     */
    public ListOfParsableVariable createParamVars(Services services, 
                                                  ProgramMethod pm,
                                                  boolean makeNamesUnique) {
        ListOfParsableVariable result = SLListOfParsableVariable.EMPTY_LIST;
        for(int i = 0; i < pm.getParameterDeclarationCount(); i++) {
            KeYJavaType parType = pm.getParameterType(i);
            String parName = pm.getParameterDeclarationAt(i)
                               .getVariableSpecification()
                               .getName();
            ProgramElementName parPEN = getNewName(services, 
                                                   parName,
                                                   makeNamesUnique);
            result = result.append(new LocationVariable(parPEN, parType));
        }        
        return result;
    }
    
    
    /**
     * Creates a program variable for the result.
     */
    public ProgramVariable createResultVar(Services services, 
                                           ProgramMethod pm,
                                           boolean makeNameUnique) {
        return (pm.getKeYJavaType() == null
                ? null
                : new LocationVariable(getNewName(services, 
                                                  "result",
                                                  makeNameUnique),
                                       pm.getKeYJavaType()));
    }
    
    
    /**
     * Creates a program variable for the thrown exception.
     */
    public ProgramVariable createExcVar(Services services, 
                                        ProgramMethod pm,
                                        boolean makeNameUnique) {
        return new LocationVariable(getNewName(services, "exc", makeNameUnique),
                                    services.getJavaInfo().getTypeByClassName(
                                                   "java.lang.Throwable"));
        
    }
}
    
