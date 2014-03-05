// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.rule.inst;

import java.util.Iterator;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.DefaultImmutableMap;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.GenericSupersortException;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;

public class TestGenericSortInstantiations extends TestCase {

    static final ImmutableSet<Sort> emptySortSet = DefaultImmutableSet.<Sort>nil();


    /**
     *
     *         A4
     *          |
     *         A3
     *        /  \
     *  A6  A1    A2
     *    \  |
     *      A5
     *
     *
     *        B4
     *       /  \
     *     B2    B3
     *    /  \  /
     *  B5    B1
     *
     *
     *        D4            (the same with array sorts)
     *       /  \
     *     D2    D3
     *    /  \  /
     *  D5    D1
     *
     *
     *        G3
     *       /  \
     *     G1    G2
     *      |
     *     G4
     *
     *
     *              A3
     *       H1    /
     *      /  \  /
     *     H2   H3
     *           |
     *          H4
     *
     *    H2 oneof { A2, A3 }
     */

    
    Sort        object;
    Sort        cloneable;
    Sort        serializable;
    
    Sort        objectArray;
    // these sorts are supposed to have no relations to other (object) sorts;
    Sort A4;
    Sort A3;
    Sort A1;
    Sort A2;
    Sort A6;
    Sort A5;
    
    Sort A4OBJ;
    Sort A3OBJ;
    Sort A1OBJ;
    Sort A2OBJ;
    Sort A6OBJ;
    Sort A5OBJ;    

    Sort B4;
    Sort B2;
    Sort B3;
    Sort B1;
    Sort B5;

    // This setup resembles the code of <code>Recoder2KeY</code>
    Sort  D4;
    Sort  D2;
    Sort  D3;
    Sort  D1;
    Sort  D5;
    
    Sort       C1;

    GenericSort G3;
    GenericSort G1;
    GenericSort G2;
    GenericSort G4;

    GenericSort H1;
    GenericSort H2;
    GenericSort H3;
    GenericSort H4;

    /*
    Function fa1 = new Function ( new Name ( "fa1" ), A1, new Sort [0] );
    Term     a1  = tf.createFunctionTerm ( fa1 );
    Function fa2 = new Function ( new Name ( "fa2" ), A2, new Sort [0] );
    Term     a2  = tf.createFunctionTerm ( fa2 );
    Function fa3 = new Function ( new Name ( "fa3" ), A3, new Sort [0] );
    Term     a3  = tf.createFunctionTerm ( fa3 );
    Function fa4 = new Function ( new Name ( "fa4" ), A4, new Sort [0] );
    Term     a4  = tf.createFunctionTerm ( fa4 );
    Function fa5 = new Function ( new Name ( "fa5" ), A5, new Sort [0] );
    Term     a5  = tf.createFunctionTerm ( fa5 );
    Function fa6 = new Function ( new Name ( "fa6" ), A6, new Sort [0] );
    Term     a6  = tf.createFunctionTerm ( fa6 );

    Function fb1 = new Function ( new Name ( "fb1" ), B1, new Sort [0] );
    Term     b1  = tf.createFunctionTerm ( fb1 );
    Function fb2 = new Function ( new Name ( "fb2" ), B2, new Sort [0] );
    Term     b2  = tf.createFunctionTerm ( fb2 );
    Function fb3 = new Function ( new Name ( "fb3" ), B3, new Sort [0] );
    Term     b3  = tf.createFunctionTerm ( fb3 );
    Function fb4 = new Function ( new Name ( "fb4" ), B4, new Sort [0] );
    Term     b4  = tf.createFunctionTerm ( fb4 );
    Function fb5 = new Function ( new Name ( "fb5" ), B5, new Sort [0] );
    Term     b5  = tf.createFunctionTerm ( fb5 );


    SchemaVariable svg1 = SchemaVariableFactory.createTermSV ( new Name ( "svg1" ), G1 );
    SchemaVariable svg1b = SchemaVariableFactory.createTermSV ( new Name ( "svg1b" ), G1 );
    SchemaVariable svg1c = SchemaVariableFactory.createTermSV ( new Name ( "svg1c" ), G1 );
    SchemaVariable svg2 = SchemaVariableFactory.createTermSV ( new Name ( "svg2" ), G2 );
    SchemaVariable svg2b = SchemaVariableFactory.createTermSV ( new Name ( "svg2b" ), G2 );
    SchemaVariable svg3 = SchemaVariableFactory.createTermSV ( new Name ( "svg3" ), G3 );
    SchemaVariable svg4 = SchemaVariableFactory.createTermSV ( new Name ( "svg4" ), G4 );


    SchemaVariable sva4 = SchemaVariableFactory.createTermSV ( new Name ( "sva4" ), A4 );
    */

    public TestGenericSortInstantiations(String name)
	throws GenericSupersortException {
	super(name);

	
    }

    @Override
    public void setUp() {
       // this ensures that necessary Java types are loaded
       TacletForTests.services ().getJavaInfo().readJavaBlock("{}");  
       
       object       = TacletForTests.services ().getJavaInfo ().objectSort ();
       cloneable    = TacletForTests.services ().getJavaInfo ().cloneableSort ();
       serializable = TacletForTests.services ().getJavaInfo ().serializableSort();

       objectArray = ArraySort.getArraySort ( object,
             object, cloneable, serializable );    
       // these sorts are supposed to have no relations to other (object) sorts;
       A4 = new SortImpl ( new Name ( "A4" ), emptySortSet, false );
       A3 = new SortImpl ( new Name ( "A3" ), emptySortSet.add ( A4 ), false );
       A1 = new SortImpl ( new Name ( "A1" ), emptySortSet.add ( A3 ), false );
       A2 = new SortImpl ( new Name ( "A2" ), emptySortSet.add ( A3 ), false );
       A6 = new SortImpl ( new Name ( "A6" ), emptySortSet, false );
       A5 = new SortImpl ( new Name ( "A5" ), emptySortSet.add ( A1 ).add ( A6 ), false );

       A4OBJ = new SortImpl ( new Name ( "A4OBJ" ), emptySortSet.add(object), false );
       A3OBJ = new SortImpl ( new Name ( "A3OBJ" ), emptySortSet.add ( A4OBJ ), false );
       A1OBJ = new SortImpl ( new Name ( "A1OBJ" ), emptySortSet.add ( A3OBJ ), false );
       A2OBJ = new SortImpl ( new Name ( "A2OBJ" ), emptySortSet.add ( A3OBJ ), false );
       A6OBJ = new SortImpl ( new Name ( "A6OBJ" ), emptySortSet, false );
       A5OBJ = new SortImpl ( new Name ( "A5OBJ" ), emptySortSet.add ( A1OBJ ).add ( A6OBJ ), false );    

       B4 = new SortImpl ( new Name ( "B4" ), emptySortSet.add ( object ), false );
       B2 = new SortImpl ( new Name ( "B2" ), emptySortSet.add ( B4 ), false );
       B3 = new SortImpl ( new Name ( "B3" ), emptySortSet.add ( B4 ), false );
       B1 = new SortImpl ( new Name ( "B1" ), emptySortSet.add ( B2 ).add ( B3 ), false );
       B5 = new SortImpl ( new Name ( "B5" ), emptySortSet.add ( B2 ), false );

       // This setup resembles the code of <code>Recoder2KeY</code>
       D4 = ArraySort.getArraySort ( B4, object, cloneable, serializable );
       D2 = ArraySort.getArraySort ( B2, object, cloneable, serializable );
       D3 = ArraySort.getArraySort ( B3, object, cloneable, serializable );
       D1 = ArraySort.getArraySort ( B1, object, cloneable, serializable );
       D5 = ArraySort.getArraySort ( B5, object, cloneable, serializable );

       C1 = new SortImpl         ( new Name ( "C1" ) );

       try {
          G3 = new GenericSort ( new Name ( "G3" ) );
           G1 = new GenericSort ( new Name ( "G1" ),
                        emptySortSet.add ( G3 ),
                        emptySortSet );
           G2 = new GenericSort ( new Name ( "G2" ),
                        emptySortSet.add ( G3 ),
                        emptySortSet );
           G4 = new GenericSort ( new Name ( "G4" ),
                        emptySortSet.add ( G1 ),
                        emptySortSet );

           H1 = new GenericSort ( new Name ( "H1" ) );
           H2 = new GenericSort ( new Name ( "H2" ),
                        emptySortSet.add ( H1 ),
                        emptySortSet.add ( A2 ).add ( A3 ) );
           H3 = new GenericSort ( new Name ( "H3" ),
                        emptySortSet.add ( A3 ).add ( H1 ),
                        emptySortSet );
           H4 = new GenericSort ( new Name ( "H4" ),
                        emptySortSet.add ( H3 ),
                        emptySortSet );
       }
       catch (GenericSupersortException e) {
          fail(e.getMessage());
       }
    }

    public static ImmutableList<GenericSort> sorts ( ImmutableList<GenericSortCondition> p_conditions ) {
	Iterator<GenericSortCondition> it = p_conditions.iterator ();
	ImmutableList<GenericSort> res = ImmutableSLList.<GenericSort>nil();

	while ( it.hasNext () )
	    res = res.prepend ( it.next ().getGenericSort () );

	return res;
    }

    /*
    public void testGeneric0 () {
	SVInstantiations svi = SVInstantiations.EMPTY_SVINSTANTIATIONS;
	svi = svi.add ( sva4, a4 );
	
	assertTrue ( "Instantiations should be equal",
		     gsi.isEmpty() );
    }
    */

    public void testGeneric1 () {
	ImmutableList<GenericSortCondition> cs;
	GenericSortInstantiations gsi;

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A4 ) );
	
	Services services = TacletForTests.services();

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A4 ),
	               gsi.getAllInstantiations () );

	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A3 ) );
	
	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A4 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A2 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A3 ),
	               gsi.getAllInstantiations () );

	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A4 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A4 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A6 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, Sort.ANY ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, B1 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, B5 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, B2 ),
	               gsi.getAllInstantiations () );
    }


    public void testGeneric2 () {
	ImmutableList<GenericSortCondition> cs;
	GenericSortInstantiations gsi;
	
	Services services = TacletForTests.services();

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, A2 ) );
	
	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A1 ).put ( G2, A2 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, B3 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A1 ).put ( G2, B3 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A2 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, B3 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, B5 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A3 ).put ( G2, B4 ),
	               gsi.getAllInstantiations () );

	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G4, A5 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A3 ).put ( G2, B4 ).put ( G4, A5 ),
	               gsi.getAllInstantiations () );

	cs = cs.tail ();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G4, A4 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A4 ).put ( G2, B4 ).put ( G4, A4 ),
	               gsi.getAllInstantiations () );

	cs = cs.tail ();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G4, B1 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, Sort.ANY ).put ( G2, B4 ).put ( G4, B1 ),
	               gsi.getAllInstantiations () );
    }


    public void testGeneric2Array () {
	ImmutableList<GenericSortCondition> cs;
	GenericSortInstantiations gsi;
	
	Services services = TacletForTests.services();

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, A2 ) );
	
	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A1 ).put ( G2, A2 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, D3 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A1 ).put ( G2, D3 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A2 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, D3 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, D5 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A3 ).put ( G2, D4 ),
	               gsi.getAllInstantiations () );

	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G4, A5 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A3 ).put ( G2, D4 ).put ( G4, A5 ),
	               gsi.getAllInstantiations () );

	cs = cs.tail ();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G4, A4 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A4 ).put ( G2, D4 ).put ( G4, A4 ),
	               gsi.getAllInstantiations () );

	cs = cs.tail ();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G4, D1 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, Sort.ANY ).put ( G2, D4 ).put ( G4, D1 ),
	               gsi.getAllInstantiations () );
    }


    public void testGeneric3 () {
	ImmutableList<GenericSortCondition> cs;
	GenericSortInstantiations gsi;
	
	Services services = TacletForTests.services();

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, A2 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G3, A5 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A1 ).put ( G2, A2 ).put ( G3, A3 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A5 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, A2 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G3, A5 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A5 ).put ( G2, A2 ).put ( G3, A3 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A5 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, A2 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G3, A5 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G4, A1 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A1 ).put ( G2, A2 ).put ( G3, A3 ).put ( G4, A1 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A5 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, A2 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G3, A5 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G4, B1 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );	
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, Sort.ANY ).put ( G2, A2 ).put ( G3, Sort.ANY ).put ( G4, B1 ),
	               gsi.getAllInstantiations () );
	
	cs =  ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A2 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, B2 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G4, A5 ) );
	
	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A3 ).put ( G2, B2 ).put ( G4, A5 ),
	               gsi.getAllInstantiations () );
    }


    public void testGeneric4 () {
	ImmutableList<GenericSortCondition> cs;
	GenericSortInstantiations gsi;
	
	Services services = TacletForTests.services();

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( G1, A4 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A4 ),
	               gsi.getAllInstantiations () );

	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A3 ) );
	
	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A4 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( G1, A1 ) );
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( G1, A2 ) );

	try {
	    gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	    fail ( "Expected GenericSortException" );
	} catch ( GenericSortException e ) {}

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1 ) );
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( G1, A2 ) );

	try {
	    gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	    fail ( "Expected GenericSortException" );
	} catch ( GenericSortException e ) {}

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( H2, A3 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( H2, A3 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( H2, A5 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( H2, A3 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( H2, A4 ) );

	try {
	    gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	    fail ( "Expected GenericSortException" );
	} catch ( GenericSortException e ) {}

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( H3, A1 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( H3, A1 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( H3, A1 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( H3, A1 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( H3, A6 ) );

	try {
	    gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	    fail ( "Expected GenericSortException" );
	} catch ( GenericSortException e ) {}

    }


    public void testGeneric5 () {
	ImmutableList<GenericSortCondition> cs;
	GenericSortInstantiations gsi;
	
	Services services = TacletForTests.services();

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( H1, A4 ) );
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( H2, A3 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( H1, A4 ).put ( H2, A3 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( H1, A6 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( H2, A5 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( H1, Sort.ANY ).put ( H2, A3 ),
	               gsi.getAllInstantiations () );
	
	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( H2, A4 ) );
	try {
	    gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	    fail ( "Expected GenericSortException" );
	} catch ( GenericSortException e ) {}
	

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( H1, A2 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( H2, A5 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( H1, A3 ).put ( H2, A3 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( H1, A2 ) );
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( H3, A5 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( H1, A3 ).put ( H3, A5 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( H1, A2 ) );
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( H3, A5 ) );

	try {
	    gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	    fail ( "Expected GenericSortException" );
	} catch ( GenericSortException e ) {}

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( H4, A6 ) );

	try {
	    gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	    fail ( "Expected GenericSortException" );
	} catch ( GenericSortException e ) {}

    }


    public void testGeneric6 () {
	ImmutableList<GenericSortCondition> cs;
	GenericSortInstantiations gsi;
	
	Services services = TacletForTests.services();

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( G1, A4 ) );
	cs = cs.prepend ( GenericSortCondition.createForceInstantiationCondition ( G4, true ) );
	cs = cs.prepend ( GenericSortCondition.createForceInstantiationCondition ( G3, false ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A4 ).put ( G4, A4 ).put ( G3, A4 ),
	               gsi.getAllInstantiations () );

	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A3 ) );
	
	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A4 ).put ( G4, A4 ).put ( G3, A4 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createIdentityCondition ( G1, A5 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G2, A2 ) );
	cs = cs.prepend ( GenericSortCondition.createForceInstantiationCondition ( G3, false ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A5 ).put ( G2, A2 ).put ( G3, A3 ),
	               gsi.getAllInstantiations () );

	cs = cs.prepend ( GenericSortCondition.createForceInstantiationCondition ( G4, true ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A5 ).put ( G2, A2 ).put ( G3, A3 ).put ( G4, A5 ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createForceInstantiationCondition ( H3, true ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( H3, A3 ),
	               gsi.getAllInstantiations () );

    }

    public void testNullsort () {
	ImmutableList<GenericSortCondition> cs;
	GenericSortInstantiations gsi;
	
	Services services = TacletForTests.services();
	Sort nullSort = new NullSort(services.getJavaInfo().objectSort());
	services.getNamespaces().sorts().add(ImmutableSLList.<Named>nil().prepend(A1OBJ)
		                                                     .prepend(A2OBJ)
		                                                     .prepend(A3OBJ)
		                                                     .prepend(A4OBJ)
		                                                     .prepend(A5OBJ)
		                                                     .prepend(A6OBJ));
	
	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1OBJ ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, nullSort ) );
	
	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A1OBJ ),
	               gsi.getAllInstantiations () );

	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A2OBJ ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A3OBJ ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, nullSort ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, A1OBJ ) );
	
	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, A1OBJ ),
	               gsi.getAllInstantiations () );
	
	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, C1 ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, nullSort ) );
	
	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, Sort.ANY ),
	               gsi.getAllInstantiations () );

	cs = ImmutableSLList.<GenericSortCondition>nil();
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, nullSort ) );
	cs = cs.prepend ( GenericSortCondition.createSupersortCondition ( G1, C1 ) );

	gsi = GenericSortInstantiations.create ( sorts ( cs ), cs, services );
	assertEquals ( "Instantiations should be equal",
	               DefaultImmutableMap.<GenericSort,Sort>nilMap()
	               .put ( G1, Sort.ANY ),
	               gsi.getAllInstantiations () );
    }

}
