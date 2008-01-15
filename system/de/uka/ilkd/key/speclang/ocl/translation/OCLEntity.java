//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl.translation;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 * A Term, a KeYJavaType, or an OCLCollection.
 */
class OCLEntity extends SLExpression {
    
    public OCLEntity(Term term) {
        super(term);
    }

    public OCLEntity(KeYJavaType type) {
        super(type);
    }

    public OCLEntity(OCLCollection collection) {
        super(collection);
    }

    /**
     * returns a collection containing only the element which is represented 
     * by the Term of this entity
     * @throws SLTranslationException 
     */
    public OCLEntity asCollection() throws SLTranslationException {
        return this.getTerm() != null ? new OCLEntity(new OCLCollection(this.getTerm())) : null;
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
            result = this.getType().getSort();
        } else if(isTerm()) {
            result = this.getTerm().sort();
        } else {
            result = this.getCollection().getElementSort();
        }
        
        return result;
    }
    
}
