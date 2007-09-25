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

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;


/**
 * A Term, a KeYJavaType, or an OCLCollection.
 */
class OCLEntity {
    private final Term term;
    private final KeYJavaType type;
    private final OCLCollection collection;
    
    
    public OCLEntity(Term term) {
        Debug.assertTrue(term != null);
        this.term       = term;
        this.type       = null;
        this.collection = null;
    }
    
    
    public OCLEntity(KeYJavaType type) {
        Debug.assertTrue(type != null);
        this.term       = null;
        this.type       = type;
        this.collection = null;
    }
    
    
    public OCLEntity(OCLCollection collection) {
        Debug.assertTrue(collection != null);
        this.term       = null;
        this.type       = null;
        this.collection = collection;
    }
    
    
    public boolean isTerm() {
        return term != null;
    }
    
    
    public boolean isType() {
        return type != null;
    }
    
    
    public boolean isCollection() {
        return collection != null;
    }
    
    
    /**
     * returns a collection containing only the element which is represented 
     * by the Term of this entity
     * @throws OCLTranslationError 
     */
    public OCLEntity asCollection() throws OCLTranslationError {
        return this.term != null ? new OCLEntity(new OCLCollection(this.term)) : null;
    }
    
    
    public Term getTerm() {
        return term;
    }
    
    
    public KeYJavaType getType() {
        return type;
    }
    
    
    public OCLCollection getCollection() {
        return collection;
    }
    
    
    /**
     * For types and terms, this method returns the corresponding sort.
     * For collections it returns the sort of the elements, the collection
     * contains.
     * 
     * @return non-collection-sort of this entity
     */
    public Sort getSort() {
        Sort result;
        
        if(isType()) {
            result = type.getSort();
        } else if(isTerm()) {
            result = term.sort();
        } else {
            result = collection.getElementSort();
        }
        
        return result;
    }
    
    
    public String toString() {
        if(isTerm()) {
            return term.toString();
        } else if(isType()) {
            return type.toString();
        } else {
            return collection.toString();
        }
    }

}
