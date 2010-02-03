// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op.oclop;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.oclsort.CollectionSort;
import de.uka.ilkd.key.logic.sort.oclsort.OclSort;

public abstract class OclOp {

    public static final Function INVARIANT = new RigidFunction(new Name("$invariant"),
							  OclSort.OCLINVARIANT,
							  new Sort[]{OclSort.OCLTYPE,
								     OclSort.BOOLEAN});

    public static final Function CONS_INV = new RigidFunction(new Name("$cons_inv"),
							 OclSort.SET_OF_OCLINVARIANT,
							 new Sort[]{OclSort.OCLINVARIANT,
								    OclSort.SET_OF_OCLINVARIANT});

    public static final Function NIL_INV = new RigidFunction(new Name("$nil_inv"),
							OclSort.SET_OF_OCLINVARIANT,
							new Sort[0]);
    
    public static final OclInsertSet INSERT_SET = new OclInsertSet();
    public static final OclInsertBag INSERT_BAG = new OclInsertBag();
    public static final OclInsertSequence INSERT_SEQUENCE = new OclInsertSequence();
    public static final OclEmptySet EMPTY_SET = new OclEmptySet();
    public static final OclEmptyBag EMPTY_BAG = new OclEmptyBag();
    public static final OclEmptySequence EMPTY_SEQUENCE = new OclEmptySequence();
    public static final OclIterate ITERATE = new OclIterate();
    public static final OclQuantifier FOR_ALL = new OclQuantifier(new Name("$forAll"));
    public static final OclQuantifier EXISTS = new OclQuantifier(new Name("$exists"));
    public static final OclQuantifier ONE = new OclQuantifier(new Name("$one"));
    public static final OclIsUnique IS_UNIQUE = new OclIsUnique();
    public static final OclSortedBy SORTED_BY = new OclSortedBy();
    public static final OclAny ANY = new OclAny();
    public static final OclSetOp INCLUDING = new OclSetOp(new Name("$including"));
    public static final OclSetOp EXCLUDING = new OclSetOp(new Name("$excluding"));
    public static final OclSequenceOp APPEND = new OclSequenceOp(new Name("$append"));
    public static final OclSequenceOp PREPEND = new OclSequenceOp(new Name("$prepend"));
    public static final OclCollectionConversion AS_SET 
	= new OclCollectionConversion(new Name("$asSet"), CollectionSort.SET);
    public static final OclCollectionConversion AS_BAG 
	= new OclCollectionConversion(new Name("$asBag"), CollectionSort.BAG);
    public static final OclCollectionConversion AS_SEQUENCE 
	= new OclCollectionConversion(new Name("$asSequence"), CollectionSort.SEQUENCE);
    public static final OclSubSequence SUB_SEQUENCE = new OclSubSequence();
    public static final OclSequenceElems AT = new OclSequenceElems(new Name("$at"), 2);
    public static final OclSequenceElems FIRST = new OclSequenceElems(new Name("$first"), 1);
    public static final OclSequenceElems LAST = new OclSequenceElems(new Name("$last"), 1);
    public static final OclIf IF = new OclIf();
    public static final Function ALL_SUBTYPES = new NonRigidFunction(new Name("$allSubtypes"),
							     //new CollectionSort(CollectionSort.SET, 
							     //		       OclSort.OCLTYPE),
							     OclSort.SET_OF_OCLTYPE,
							     new Sort[]{OclSort.OCLTYPE});
    public static final Function ALL_INSTANCES = new NonRigidFunction(new Name("$allInstances"),
							      //new CollectionSort(CollectionSort.SET, 
							      //		   OclSort.CLASSIFIER),
							      OclSort.SET_OF_CLASSIFIER,
							      new Sort[]{OclSort.OCLTYPE});
    public static final OclUnion UNION = new OclUnion();
    public static final OclIntersection INTERSECTION = new OclIntersection();
    public static final OclDifference DIFFERENCE = new OclDifference(new Name("$difference"));
    public static final OclDifference SYMMETRIC_DIFFERENCE 
	= new OclDifference(new Name("$symmetricDifference"));
    public static final OclSubsetOp SELECT = new OclSubsetOp(new Name("$select"));
    public static final OclSubsetOp REJECT = new OclSubsetOp(new Name("$reject"));
    public static final OclCollect COLLECT = new OclCollect();
    public static final Function AND = new RigidFunction(new Name("$and"),
						    OclSort.BOOLEAN,
						    new Sort[]{OclSort.BOOLEAN, OclSort.BOOLEAN});
    public static final Function OR = new RigidFunction(new Name("$or"),
						   OclSort.BOOLEAN,
						   new Sort[]{OclSort.BOOLEAN, OclSort.BOOLEAN});
    public static final Function XOR = new RigidFunction(new Name("$xor"),
						    OclSort.BOOLEAN,
						    new Sort[]{OclSort.BOOLEAN, OclSort.BOOLEAN});
    public static final Function IMPLIES 
	= new RigidFunction(new Name("$implies"),
		       OclSort.BOOLEAN,
		       new Sort[]{OclSort.BOOLEAN, OclSort.BOOLEAN});
    public static final Function NOT = new RigidFunction(new Name("$not"),
						    OclSort.BOOLEAN,
						    new Sort[]{OclSort.BOOLEAN});
    public static final Function EQUALS = new NonRigidFunction(new Name("$equals"),
						       OclSort.BOOLEAN,
						       new Sort[]{OclSort.OCLGENERIC, 
								  OclSort.OCLGENERIC});
    public static final Function NOT_EQUALS = new NonRigidFunction(new Name("$notEquals"),
							   OclSort.BOOLEAN,
							   new Sort[]{OclSort.OCLGENERIC, 
								      OclSort.OCLGENERIC});
    public static final Function OCL_IS_NEW = new NonRigidFunction(new Name("$oclIsNew"),
							   OclSort.BOOLEAN,
							   new Sort[]{OclSort.CLASSIFIER});
    public static final Function TRUE = new RigidFunction(new Name("$true"),
						     OclSort.BOOLEAN,
						     new Sort[0]);
    public static final Function FALSE = new RigidFunction(new Name("$false"),
						      OclSort.BOOLEAN,
						      new Sort[0]);
    public static final Function SELF = new NonRigidFunction(new Name("$self"),
						     OclSort.CLASSIFIER,
						     new Sort[0]);
    public static final Function INCLUDES = new RigidFunction(new Name("$includes"),
							 OclSort.BOOLEAN,
							 new Sort[]{OclSort.COLLECTION_OF_OCLANY,
								    OclSort.OCLANY});
    public static final Function EXCLUDES = new RigidFunction(new Name("$excludes"),
							 OclSort.BOOLEAN,
							 new Sort[]{OclSort.COLLECTION_OF_OCLANY,
								    OclSort.OCLANY});
    public static final Function COUNT = new RigidFunction(new Name("$count"),
						      OclSort.INTEGER,
						      new Sort[]{OclSort.COLLECTION_OF_OCLANY,
								 OclSort.OCLANY});
    public static final Function INCLUDES_ALL 
	= new RigidFunction(new Name("$includesAll"),
		       OclSort.BOOLEAN,
		       new Sort[]{OclSort.COLLECTION_OF_OCLANY,
				  OclSort.COLLECTION_OF_OCLANY});
    public static final Function EXCLUDES_ALL 
	= new RigidFunction(new Name("$excludesAll"),
		       OclSort.BOOLEAN,
		       new Sort[]{OclSort.COLLECTION_OF_OCLANY,
				  OclSort.COLLECTION_OF_OCLANY});
    public static final Function SIZE = new RigidFunction(new Name("$size"),
						     OclSort.INTEGER,
						     new Sort[]{OclSort.COLLECTION_OF_OCLANY});
    public static final Function IS_EMPTY = new RigidFunction(new Name("$isEmpty"),
							 OclSort.BOOLEAN,
							 new Sort[]{OclSort.COLLECTION_OF_OCLANY});
    public static final Function NOT_EMPTY = new RigidFunction(new Name("$notEmpty"),
							  OclSort.BOOLEAN,
							  new Sort[]{OclSort.COLLECTION_OF_OCLANY});
    public static final Function SUM = new RigidFunction(new Name("$sum"),
						    OclSort.REAL,
						    new Sort[]{OclSort.COLLECTION_OF_REAL});

    public static final Function LESS_THAN = new RigidFunction(new Name("$lessThan"),
							  OclSort.BOOLEAN,
							  new Sort[]{OclSort.REAL,
								     OclSort.REAL});
    public static final Function LESS_THAN_EQ = new RigidFunction(new Name("$lessThanEq"),
							     OclSort.BOOLEAN,
							     new Sort[]{OclSort.REAL,
									OclSort.REAL});
    public static final Function GREATER_THAN = new RigidFunction(new Name("$greaterThan"),
							     OclSort.BOOLEAN,
							     new Sort[]{OclSort.REAL,
									OclSort.REAL});
    public static final Function GREATER_THAN_EQ = new RigidFunction(new Name("$greaterThanEq"),
								OclSort.BOOLEAN,
								new Sort[]{OclSort.REAL,
									   OclSort.REAL});
    public static final Function PLUS = new RigidFunction(new Name("$plus"),
						     OclSort.REAL,
						     new Sort[]{OclSort.REAL,
								OclSort.REAL});
    public static final Function MINUS = new RigidFunction(new Name("$minus"),
						      OclSort.REAL,
						      new Sort[]{OclSort.REAL,
								 OclSort.REAL});
    public static final Function TIMES = new RigidFunction(new Name("$times"),
						      OclSort.REAL,
						      new Sort[]{OclSort.REAL,
								 OclSort.REAL});
    public static final Function DIV_INFIX = new RigidFunction(new Name("$divInfix"),
							  OclSort.REAL,
							  new Sort[]{OclSort.REAL,
								     OclSort.REAL});
    public static final Function DIV = new RigidFunction(new Name("$div"),
						    OclSort.INTEGER,
						    new Sort[]{OclSort.INTEGER,
							       OclSort.INTEGER});
    public static final Function MOD = new RigidFunction(new Name("$mod"),
						    OclSort.INTEGER,
						    new Sort[]{OclSort.INTEGER,
							       OclSort.INTEGER});
    public static final Function MIN = new RigidFunction(new Name("$min"),
						    OclSort.REAL,
						    new Sort[]{OclSort.REAL,
							       OclSort.REAL});
    public static final Function MAX = new RigidFunction(new Name("$max"),
						    OclSort.REAL,
						    new Sort[]{OclSort.REAL,
							       OclSort.REAL});
    public static final Function MINUS_PREFIX = new RigidFunction(new Name("$plus"),
							     OclSort.REAL,
							     new Sort[]{OclSort.REAL});
    public static final Function ABS = new RigidFunction(new Name("$abs"),
						    OclSort.REAL,
						    new Sort[]{OclSort.REAL});

    public static final Function OCL_WRAPPER = new NonRigidFunction(new Name("$OclWrapper"),
							    Sort.FORMULA,
							    new Sort[]{OclSort.OCLGENERIC});
}
