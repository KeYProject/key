// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.sort.oclsort;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

public interface OclSort extends Sort {
    
    //For OCL simplification
    OclInvariantSort OCLINVARIANT = new OclInvariantSort(new Name("OclInvariant"));

    OclGenericSort OCLGENERIC = new OclGenericSort(new Name("OclGeneric"));
    OclAnySort OCLANY = new OclAnySort(new Name("OclAny"));
    OclTypeSort OCLTYPE = new OclTypeSort(new Name("OclType"));
    BooleanSort BOOLEAN = new BooleanSort(new Name("OclBoolean"));
    RealSort REAL = new RealSort(new Name("OclReal"));
    IntegerSort INTEGER = new IntegerSort(new Name("OclInteger"));
    StringSort STRING = new StringSort(new Name("OclString"));
    ClassifierSort CLASSIFIER = new ClassifierSort(new Name("OclClassifier")); 

    CollectionSort COLLECTION_OF_OCLGENERIC 
	= new CollectionSort(CollectionSort.COLLECTION, OCLGENERIC);
    CollectionSort COLLECTION_OF_OCLANY 
	= new CollectionSort(CollectionSort.COLLECTION, OCLANY);
    CollectionSort COLLECTION_OF_OCLTYPE 
	= new CollectionSort(CollectionSort.COLLECTION, OCLTYPE);
    CollectionSort COLLECTION_OF_BOOLEAN 
	= new CollectionSort(CollectionSort.COLLECTION, BOOLEAN);
    CollectionSort COLLECTION_OF_REAL 
	= new CollectionSort(CollectionSort.COLLECTION, REAL);
    CollectionSort COLLECTION_OF_INTEGER 
	= new CollectionSort(CollectionSort.COLLECTION, INTEGER);
    CollectionSort COLLECTION_OF_STRING 
	= new CollectionSort(CollectionSort.COLLECTION, STRING);
    CollectionSort COLLECTION_OF_CLASSIFIER 
	= new CollectionSort(CollectionSort.COLLECTION, CLASSIFIER);

    CollectionSort SET_OF_OCLINVARIANT 
	= new CollectionSort(CollectionSort.SET, OCLINVARIANT);
    CollectionSort SET_OF_OCLGENERIC 
	= new CollectionSort(CollectionSort.SET, OCLGENERIC);
    CollectionSort SET_OF_OCLANY 
	= new CollectionSort(CollectionSort.SET, OCLANY);
    CollectionSort SET_OF_OCLTYPE 
	= new CollectionSort(CollectionSort.SET, OCLTYPE);
    CollectionSort SET_OF_BOOLEAN 
	= new CollectionSort(CollectionSort.SET, BOOLEAN);
    CollectionSort SET_OF_REAL 
	= new CollectionSort(CollectionSort.SET, REAL);
    CollectionSort SET_OF_INTEGER 
	= new CollectionSort(CollectionSort.SET, INTEGER);
    CollectionSort SET_OF_STRING 
	= new CollectionSort(CollectionSort.SET, STRING);
    CollectionSort SET_OF_CLASSIFIER 
	= new CollectionSort(CollectionSort.SET, CLASSIFIER);

    CollectionSort BAG_OF_OCLGENERIC 
	= new CollectionSort(CollectionSort.BAG, OCLGENERIC);
    CollectionSort BAG_OF_OCLANY 
	= new CollectionSort(CollectionSort.BAG, OCLANY);
    CollectionSort BAG_OF_OCLTYPE 
	= new CollectionSort(CollectionSort.BAG, OCLTYPE);
    CollectionSort BAG_OF_BOOLEAN 
	= new CollectionSort(CollectionSort.BAG, BOOLEAN);
    CollectionSort BAG_OF_REAL 
	= new CollectionSort(CollectionSort.BAG, REAL);
    CollectionSort BAG_OF_INTEGER 
	= new CollectionSort(CollectionSort.BAG, INTEGER);
    CollectionSort BAG_OF_STRING 
	= new CollectionSort(CollectionSort.BAG, STRING);
    CollectionSort BAG_OF_CLASSIFIER 
	= new CollectionSort(CollectionSort.BAG, CLASSIFIER);

    CollectionSort SEQUENCE_OF_OCLGENERIC 
	= new CollectionSort(CollectionSort.SEQUENCE, OCLGENERIC);
    CollectionSort SEQUENCE_OF_OCLANY 
	= new CollectionSort(CollectionSort.SEQUENCE, OCLANY);
    CollectionSort SEQUENCE_OF_OCLTYPE 
	= new CollectionSort(CollectionSort.SEQUENCE, OCLTYPE);
    CollectionSort SEQUENCE_OF_BOOLEAN 
	= new CollectionSort(CollectionSort.SEQUENCE, BOOLEAN);
    CollectionSort SEQUENCE_OF_REAL 
	= new CollectionSort(CollectionSort.SEQUENCE, REAL);
    CollectionSort SEQUENCE_OF_INTEGER 
	= new CollectionSort(CollectionSort.SEQUENCE, INTEGER);
    CollectionSort SEQUENCE_OF_STRING 
	= new CollectionSort(CollectionSort.SEQUENCE, STRING);
    CollectionSort SEQUENCE_OF_CLASSIFIER 
	= new CollectionSort(CollectionSort.SEQUENCE, CLASSIFIER);
}
