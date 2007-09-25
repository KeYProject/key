//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.parser.ocl;




interface PropertyResolver {
        
    /**
     * Resolves property calls on explicit receivers.
     * @param receiver receiver (may *not* be null)
     * @param name name of the property
     * @param parameters the actual parameters, or null if not applicable
     * @return a suitable term or collection if successful, null otherwise
     */
    public OCLEntity resolve(OCLEntity receiver,
                             String name, 
                             OCLParameters parameters) throws OCLTranslationError;
    
    /**
     * Determines whether a propertyCall needs a declaration of a variable
     * @param propertyName name of the propertyCall
     * @return true, if propertyName needs a variable to be declarated
     */
    public boolean needVarDeclaration(String propertyName);
    
}
