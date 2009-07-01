// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/**
 * 
 */
package de.uka.ilkd.key.proof.mgt;

import java.util.HashSet;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * represents a class of modalities which are to be treated the same way 
 * by the AbstractMethodLemmaFactory. It provides access to a normal 
 * representative of the class (used to give concrete proof obligations for 
 * the method lemma) and schema modal operators representing the class (used 
 * in the method lemma taclets themselves).
 *
 */
class ModalityClass {

    /**
     * the standard pre-defined classes.
     */
    private final static ModalityClass[] DEFAULT_CLASSES = new ModalityClass[] {
        new ModalityClass(new Modality[]{Op.DIA}),
        new ModalityClass(new Modality[]{Op.BOX}),
        new ModalityClass(new Modality[]{})
    };
    
    private ModalOperatorSV schema;
    private Modality[] modalities;
    
    /**
     * creates a modality class consisting of the given modalities. The first 
     * element of the argument array is the normal representative of the 
     * class. 
     * @param mods the array of modalities seen as one modality class
     */
    public ModalityClass(Modality[] mods) {
        HashSet s = new HashSet();
        for (int i=0; i<mods.length; i++) {
            s.add(mods[i]);
        }
        schema = (ModalOperatorSV) SchemaVariableFactory.createOperatorSV
        (new Name(mods[0].name()+"_schema"), Modality.class, Sort.FORMULA, 1, s);
        modalities = mods;
    }
    
    /**
     * returns the normal representative from the pre-defined classes for the
     * given modality. If not found in the pre-defined classes the argument 
     * is returned
     */
    public static Modality getNormReprModality(Modality m) {
        for (int i=0; i<DEFAULT_CLASSES.length; i++) {
            if (DEFAULT_CLASSES[i].containsConcrete(m)) {
                return DEFAULT_CLASSES[i].getNormRepr();
            }
        }
        return m;
    }
    
    /**
     * returns the schema operator from the pre-defined classes fitting to the
     * given modality. Of not found in the pre-defined classes the argument 
     * is returned
     */    
    public static Operator getSchemaModality(Modality m) {
        for (int i=0; i<DEFAULT_CLASSES.length; i++) {
            if (DEFAULT_CLASSES[i].containsConcrete(m)) {
                return DEFAULT_CLASSES[i].getSchema();
            }
        }
        return m;      
    }

    
    /** returns the schema modal operator representing this modality class */
    public ModalOperatorSV getSchema() {
        return schema;
    }
    
    /** returns the normal representative modality of this modality class */
    public Modality getNormRepr() {
        return modalities[0];
    }
    
    /** returns true iff the modalities of this class include the given 
     * modality argument */
    public boolean containsConcrete(Modality mod) {
        return schema.operators().contains(mod);
    }
}
