// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ArraySortImpl;
import de.uka.ilkd.key.logic.sort.ClassInstanceSortImpl;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPairImpl;
import de.uka.ilkd.key.rule.updatesimplifier.Update;


/**
 *
 */
public class TestUpdateFactory extends TestCase {
    
//    private static final TermBuilder TB = TermBuilder.DF;
//    private static final TermFactory tf = TermFactory.DEFAULT;
//
//    private Proof proof;
//    
//    private Namespace variables = new Namespace();
//    private Namespace functions = new Namespace();
//    private Namespace sorts     = new Namespace();
//    
//    private ProgramVariable[] pv;
//
//    private Sort testSort0;
//    private Sort testSort1;
//    private Sort testSort2;
//    private Sort cloneable;
//    private Sort serializable;
//    private Sort integerSort;
//
//
//    // t : testSort1
//    private Term t;
//    // i : testSort1
//    private Term i;
//    // o : testSort1
//    private Term o;
//    // u : testSort1
//    private Term u;
//    // o.a 
//    private Term oa;
//    // u.a 
//    private Term ua;
//
//    private Term phi;
//    private Term psi;
//    
//    // arrays
//    private ArraySort arraySort1;
//    private ArraySort arraySort2;
//
//    private Term a;
//    private Term b;
//    
//    private NonRigidFunction nonRigidTargetOp;
//    private Term nonRigidTarget;
//
//    // var : variable of integerSort
//    private QuantifiableVariable var;
//    private Term varT;
//    
//    // var2 : variable of integerSort
//    private QuantifiableVariable var2;
//    private Term var2T;
//    
//    // f: int * int -> int
//    private Function f;
//    
//    // f(var, var2)
//    private Term fvarvar2;
//    
//    // a[var] : array of testSort 1
//    private Term avar;
//    // b[var] : array of testSort 1
//    private Term bvar;
//    // a[var2] : array of testSort 1
//    private Term avar2;
//    // a[f(var,var2)] : array of testSort 1
//    private Term avarvar2;
//    // b[var2] : array of testSort 1
//    private Term bvar2;
//
//    private Function woRelation;
//
//    private UpdateSimplifier simplifier;
//   
//    
//    public TestUpdateFactory (String s) {
//        super ( s );
//    }
//
//    public void setUp () {
//        testSort0 = new ClassInstanceSortImpl ( new Name ( "testSort0" ), false );
//        testSort1 = new ClassInstanceSortImpl ( new Name ( "testSort1" ),
//                                                testSort0, false );
//        testSort2 = new ClassInstanceSortImpl ( new Name ( "testSort2" ),
//                                                testSort0, false );
//        cloneable = new ClassInstanceSortImpl ( new Name ( "cloneable" ),
//                testSort1, false );
//
//        serializable = new ClassInstanceSortImpl ( new Name ( "serializable" ),
//                testSort1, false );
//
//        KeYJavaType kjt = new KeYJavaType ( new ClassDeclaration ( new ProgramElementName ( "Object" ),
//                                                                   new ProgramElementName ( "java.lang.Object" ) ),
//                                            testSort1 );
//        sorts.add ( testSort0 );
//        sorts.add ( testSort1 );
//        sorts.add ( testSort2 );
//        sorts.add ( cloneable );
//        sorts.add ( serializable );
//
//        pv = new ProgramVariable[7];
//        for ( int i = 0; i < pv.length; i++ ) {
//            ProgramElementName name;
//            switch ( i ) {
//            case 1:
//                name = new ProgramElementName ( "t" );
//                break;
//            case 2:
//                name = new ProgramElementName ( "i" );
//                break;
//            case 3:
//                name = new ProgramElementName ( "o" );
//                break;
//            case 4:
//                name = new ProgramElementName ( "u" );
//                break;
//            case 5:
//                name = new ProgramElementName ( "a" );
//                break;
//            default:
//                name = new ProgramElementName ( "pv" + i );
//                break;
//            }
//            pv[i] = new LocationVariable ( name, kjt );
//            variables.add ( pv[i] );
//        }      
//
//        // just initialize the parser
//        parseTerm ( "{t:=i} o" );
//        // for the systematic tests
//
//        t = tf.createFunctionTerm ( pv[1] );
//        i = tf.createFunctionTerm ( pv[2] );
//        o = tf.createFunctionTerm ( pv[3] );
//        u = tf.createFunctionTerm ( pv[4] );
//
//        oa = tf.createAttributeTerm ( pv[5], o );
//        ua = tf.createAttributeTerm ( pv[5], u );
//
//        arraySort1 = ArraySortImpl.getArraySort ( testSort1,
//                                                  testSort0,
//                                                  cloneable,
//                                                  serializable);
//        arraySort2 = ArraySortImpl.getArraySort ( testSort2,
//                                                  testSort0,
//                                                  cloneable,
//                                                  serializable);
//
//        ProgramVariable a_var = new LocationVariable ( new ProgramElementName ( "_a" ),
//                                                      arraySort1 );
//        ProgramVariable b_var = new LocationVariable ( new ProgramElementName ( "_b" ),
//                                                      arraySort1 );
//        ProgramVariable c_var = new LocationVariable ( new ProgramElementName ( "_c" ),
//                                                      arraySort2 );
//
//        functions.add ( a_var );
//        functions.add ( b_var );
//        functions.add ( c_var );
//        
//        a = tf.createFunctionTerm ( a_var );
//        b = tf.createFunctionTerm ( b_var );      
//
//        final Services services = TacletForTests.services();
//	integerSort = services.getTypeConverter().getIntegerLDT().targetSort();
//        sorts.add(integerSort);
//        
//        nonRigidTargetOp = new NonRigidFunction ( new Name ( "target" ),
//                                                  Sort.FORMULA,
//                                                  new Sort [0] );
//        functions.add ( nonRigidTargetOp );
//        nonRigidTarget = tf.createFunctionTerm ( nonRigidTargetOp );
//
//        Function phiSym = new RigidFunction ( new Name ( "phi" ),
//                                         Sort.FORMULA,
//                                         new Sort [0] );
//        functions.add ( phiSym );
//        phi = tf.createFunctionTerm ( phiSym );
//
//        Function psiSym = new RigidFunction ( new Name ( "psi" ),
//                                         Sort.FORMULA,
//                                         new Sort [0] );
//        functions.add ( psiSym );
//        psi = tf.createFunctionTerm ( psiSym );
//        
//        f = new RigidFunction(new Name("f"), integerSort,
//                              new Sort[] { integerSort, integerSort });
//        functions.add(f);
//        
//        var = new LogicVariable ( new Name ( "var" ), integerSort );
//        varT = tf.createVariableTerm ( (LogicVariable)var );
//        
//        avar = TB.array(services, a, varT);
//        bvar = TB.array(services, b, varT);
//            
//        var2 = new LogicVariable ( new Name ( "var2" ), integerSort );
//        var2T = tf.createVariableTerm ( (LogicVariable)var2 );
//        
//        avar2 = TB.array(services, a, var2T);
//        bvar2 = TB.array(services, b, var2T);
//
//        fvarvar2 = tf.createFunctionTerm ( f, varT, var2T );
//        avarvar2 = TB.array(services, a, fvarvar2);            
//        
//        woRelation = new RigidFunction ( new Name ( "quanUpdateLeqInt" ),
//                                    Sort.FORMULA,
//                                    new Sort [] {integerSort, integerSort} );
//        functions.add(woRelation);
//        
//        proof = new Proof ( TacletForTests.services () );
//        proof.setSimplifier ( new UpdateSimplifier () );
//        
//        Goal g=new Goal(new Node(proof, Sequent.EMPTY_SEQUENT), 
//            new RuleAppIndex(new TacletAppIndex(new TacletIndex()),
//                     new BuiltInRuleAppIndex
//                     (new BuiltInRuleIndex())));
//        proof.setRoot ( g.node() );
//        proof.add(g);
//        
//        proof.setNamespaces ( new NamespaceSet ( new Namespace (),
//                                                 functions,
//                                                 sorts,
//                                                 new Namespace (),
//                                                 new Namespace (),
//                                                 variables ) );
//        simplifier = proof.getSettings().
//        	getSimultaneousUpdateSimplifierSettings().getSimplifier();
//    }
//
//    public void tearDown() {
//        clear(null, null, null, null, null, null, null, null,
//                null, null, null, null, null, null, null, null, 
//                null, null, null, null, null, null, null, null, 
//                null, null, null, null, null, null, null, null, 
//                null, null, null, null, null, null, null);                 
//    }
//
//
//    private Term parseTerm (String termstr) {
//        return TacletForTests.parseTerm ( termstr,
//                                          new NamespaceSet ( new Namespace (),
//                                                             functions,
//                                                             sorts,
//                                                             new Namespace (),
//                                                             new Namespace (),
//                                                             variables ) );
//    }
//
//    private void assertEqualUpdates (final Update u1, final Update u2) {
//        assertEquals ( "Updates are expected to be equal: " + u1 + " and " + u2,
//                       u1.locationCount (),
//                       u2.locationCount () );
//        for ( int i = 0; i != u1.locationCount (); ++i )
//            assertEquals ( "Updates are expected to be equal: " + u1 + " and "
//                           + u2, u1.location ( i ), u2.location ( i ) );
//    }
//
//    private void assertEqualsModRenaming (Term t1, Term expected) {
//        assertTrue ( "Expected " + expected + ", but got " + t1,
//                     t1.equalsModRenaming ( expected ) );
//    }
//    
//    private void assertUnequalsModRenaming (Term t1, Term expected) {
//        assertFalse ( "Got something which is explicitly wrong: " + t1,
//                      t1.equalsModRenaming ( expected ) );
//    }
//    
//    public void testElementaryPVUpdates () {
//	final Services services = proof.getServices();
//        final UpdateFactory fac = new UpdateFactory ( services, 
//                simplifier );
//
//        final Update u1 = fac.elementaryUpdate ( t, i );
//        assertEquals ( proof.simplifier().simplify ( u1, 
//        					     nonRigidTarget, 
//        					     services ),
//                       parseTerm ( "{t := i} target" ) );
//
//        final Update u2 = fac.skip ();
//        assertEquals ( proof.simplifier().simplify ( u2, 
//        					     nonRigidTarget, 
//        					     services ),
//                       tf.createUpdateTerm ( services,
//                	       		     new Term [0],
//                                             new Term [0],
//                                             nonRigidTarget ) );
//
//        final Update u3 = fac.parallel (u1, u2);
//        assertEqualUpdates ( u1, u3 );
//
//        final Update u4 = fac.elementaryUpdate ( t, o );
//        assertEquals ( proof.simplifier().simplify ( u4, 
//        					     nonRigidTarget, 
//        					     services ),
//                       parseTerm ( "{t := o} target" ) );
//
//        final Update u5 = fac.parallel ( u1, u4 );
//        assertEquals ( parseTerm ( "{t := o} target" ),
//                       proof.simplifier().simplify ( u5, 
//                	       			     nonRigidTarget, 
//                	       			     services ) );
//
//        final Update u6 = fac.sequential ( u1, u4 );
//        assertEquals ( parseTerm ( "{t := o} target" ),
//                       proof.simplifier().simplify ( u6, 
//                	       			     nonRigidTarget,
//                	       			     services) );
//    }
//
//    public void testElementaryAttrUpdates () {
//	final Services services = proof.getServices();
//        final UpdateFactory fac = new UpdateFactory ( services, 
//                simplifier );
//
//        final Update u1 = fac.elementaryUpdate ( o, u );
//        assertEquals ( proof.simplifier().simplify ( u1, 
//        				             nonRigidTarget, 
//        				             services ),
//                       parseTerm ( "{o := u} target" ) );
//         
//        final Update u2 = fac.elementaryUpdate ( oa, i );
//        final AssignmentPairImpl wanted2 =
//            new AssignmentPairImpl ( (Location)oa.op (),
//                                     new Term [] { oa.sub ( 0 ) },
//                                     i );
//        assertTrue ( "Unexpected update: " + u2 + ", expected " + wanted2,
//                     u2.locationCount () == 1
//                     && u2.getAssignmentPair ( 0 ).equals ( wanted2 ) );
//
//        final Update u3 = fac.elementaryUpdate ( ua, i );
//        final AssignmentPairImpl wanted3 =
//            new AssignmentPairImpl ( (Location)ua.op (),
//                                     new Term [] { ua.sub ( 0 ) },
//                                     i );
//        assertTrue ( "Unexpected update: " + u3 + ", expected " + wanted3,
//                     u3.locationCount () == 1
//                     && u3.getAssignmentPair ( 0 ).equals ( wanted3 ) );
//
//        final Update u4 = fac.parallel ( u1, u3 );
//        final Update u5 = fac.sequential ( u1, u2 );
//        final Update u6 = fac.sequential ( u3, u1 );
//        assertEqualUpdates ( u4, u5 );        
//        assertEquals ( proof.simplifier().simplify ( u4, 
//        					     nonRigidTarget, 
//        					     services ),
//                       proof.simplifier().simplify ( u6, 
//                	       			     nonRigidTarget, 
//                	       			     services ) );
//    }
//    
//    public void testGuardedUpdates () {
//	final Services services = proof.getServices();
//        final UpdateFactory fac = new UpdateFactory ( services, 
//                simplifier );
//
//        final Update u1 = fac.guard ( phi, fac.elementaryUpdate ( o, u ) );
//        assertEquals ( proof.simplifier().simplify ( u1, 
//        					     nonRigidTarget, 
//        					     services ),
//                       parseTerm ( "{\\if (phi) o := u} target" ) );
//        
//        final Update u2 = fac.parallel ( u1, fac.elementaryUpdate ( t, i ) );
//        assertEquals ( proof.simplifier().simplify ( u2, 
//        					     nonRigidTarget,
//        					     services),
//                       parseTerm ( "{\\if (phi) o := u || t := i} target" ) );
//        
//        final Update u3 = fac.guard ( psi, u2 );
//        assertEquals ( proof.simplifier().simplify ( u3, 
//        					     nonRigidTarget,
//        					     services),
//                       parseTerm ( "{\\if (psi & phi) o := u || \\if (psi) t := i} target" ) );
//        
//        final Update u4 = fac.guard ( tf.createJunctorTerm ( Op.TRUE ), u3 );
//        assertEqualUpdates ( u3, u4 );
//        
//        final Update u5 = fac.guard ( tf.createJunctorTerm ( Op.FALSE ), u3 );
//        assertEquals ( proof.simplifier().simplify ( fac.skip(), 
//        					     nonRigidTarget,
//        					     services),
//                       proof.simplifier().simplify ( u5, 
//                	       			     nonRigidTarget,
//                	       			     services) );
//    }
//    
//    public void testQuantifiedUpdates () {
//        // the following test very much reflect the current state of optimizing
//        // the UpdateFactory; the particular shape of guards could change a lot
//        // later
//	
//        final Services services = proof.getServices();
//        final UpdateFactory fac = new UpdateFactory ( services, 
//                simplifier );
//        final Update u1 = fac.quantify ( var, fac.elementaryUpdate ( avar, u ) );
//        assertEqualsModRenaming ( proof.simplifier().simplify ( u1, 
//        						        nonRigidTarget, 
//        						        services ),
//                                  parseTerm ( "{\\for int var; _a[var] := u} target" ) );
//
//        // subsumption
//        final Update u2 = fac.parallel ( u1, u1 );
//        final Update u3 = fac.sequential ( u1, u1 );
//        assertEqualsModRenaming ( proof.simplifier().simplify ( u2, 
//        							nonRigidTarget, 
//        							services ),
//                                  parseTerm ( "{\\for int var; _a[var] := u} target" ) );
//        assertEqualsModRenaming ( proof.simplifier().simplify ( u3, 
//        							nonRigidTarget,
//        							services),
//                                  parseTerm ( "{\\for int var; _a[var] := u} target" ) );
//
//        // quantifying a variable twice is meaningless
//        final Update u4 = fac.quantify ( var, u1 );
//        assertEqualUpdates ( u1, u4 );
//
//        final Update u5 = fac.quantify ( var,
//                                         fac.parallel ( fac.elementaryUpdate ( avar, u ),
//                                                        fac.elementaryUpdate ( bvar, u ) ) );
//        assertEqualsModRenaming ( proof.simplifier ().simplify ( u5, 
//        							 nonRigidTarget,
//        							 services),
//                                  parseTerm ( "{\\for int var; _a[var] := u ||"
//                                              + "\\for int var; \\if (\\forall int varPrime; (quanUpdateLeqInt(var,varPrime) | !(_b=_a & var=varPrime))) _b[var] := u} target" ) );
//
//        final Update u10 = fac.quantify ( var,
//                                          fac.parallel ( fac.quantify ( var, fac.elementaryUpdate ( avar, u ) ),
//                                                         fac.elementaryUpdate ( bvar, u ) ) );
//        assertEqualsModRenaming ( proof.simplifier ().simplify ( u10, 
//        							 nonRigidTarget,
//        							 services),
//                                  parseTerm ( "{\\for int var; _a[var] := u ||"
//                                              + "\\for int var; \\if (\\forall int varPrime; (quanUpdateLeqInt(var,varPrime) | !_b=_a)) _b[var] := u} target" ) );
//
//        final Update u11 = fac.quantify ( var,
//                                          fac.parallel ( fac.elementaryUpdate ( bvar, u ),
//                                                         fac.quantify ( var, fac.elementaryUpdate ( avar, u ) ) ) );
//        assertEqualsModRenaming ( proof.simplifier ().simplify ( u11, 
//        							 nonRigidTarget,
//        							 services),
//                                  parseTerm ( "{\\for int var; _b[var] := u ||"
//                                              + "\\for int var; _a[var] := u} target" ) );
//        assertUnequalsModRenaming ( proof.simplifier ().simplify ( u11, 
//        							   nonRigidTarget,
//        							   services),
//                                    parseTerm ( "{\\for int var; _a[var] := u ||"
//                                                + "\\for int var; _b[var] := u} target" ) );
//
//        final Update u6 = fac.quantify ( var, fac.elementaryUpdate ( o, u ) );
//        assertEqualsModRenaming ( proof.simplifier().simplify ( u6, 
//        							nonRigidTarget,
//        							services),
//                                  parseTerm ( "{o := u} target" ) );
//        
//        final Update u7 = fac.quantify ( var,
//                                         fac.parallel ( u5,
//                                                        fac.elementaryUpdate ( o, avar ) ) );
//        assertEqualsModRenaming ( proof.simplifier ().simplify ( u7, 
//        						         nonRigidTarget,
//        						         services),
//                                  parseTerm ( "{\\for int var; _a[var] := u ||"
//                                              + "\\for int var; \\if (\\forall int varPrime; (quanUpdateLeqInt(var,varPrime) | !(_b=_a & var=varPrime))) _b[var] := u ||" +
//                                                "\\for int var; o := _a[var]} target" ) );
//        
//        final Update u8 = fac.guard ( tf.createFunctionTerm(woRelation, varT, var2T),
//                                      fac.elementaryUpdate ( avar, bvar2 ) );
//        final Update u9 = fac.quantify ( var2, fac.quantify ( var, u8 ) );
//        assertEqualsModRenaming ( proof.simplifier().simplify ( u9, 
//        						        nonRigidTarget,
//        						        services),
//                                  parseTerm ( "{\\for (int var2; int var) \\if(quanUpdateLeqInt(var, var2)) _a[var] := _b[var2]} target" ) );
//
//        final Update u12 = fac.quantify ( var,
//                                          fac.parallel ( fac.elementaryUpdate ( bvar, u ),
//                                                         fac.quantify ( var2, fac.elementaryUpdate ( avarvar2, u ) ) ) );
//        assertEqualsModRenaming ( proof.simplifier ().simplify ( u12, 
//        							 nonRigidTarget,
//        							 services),
//                                  parseTerm ( "{\\for int var; _b[var] := u || "
//                                              + "\\for (int var; int var2)" +
//                                                "  \\if (\\forall int varPrime;" +
//                                                "        (quanUpdateLeqInt(var,varPrime) |" +
//                                                "         !(_a=_b & f(var,var2)=varPrime))) _a[f(var,var2)] := u} target" ) );
//    }
//    
//    public void testConstruction() {
//	final Services services = proof.getServices();
//        final UpdateFactory fac = new UpdateFactory ( services, 
//                simplifier );
//
//        final Update u1 = fac.quantify ( var,
//                                         fac.elementaryUpdate ( avar, bvar ) );
//
//        // the same by directly using the TermFactory; we are using two
//        // different bound variables for different subterms (that have to be
//        // unified by QuanUpdateOperator)
//        final Term[] subTerms = new Term [] { a, var2T, bvar, nonRigidTarget };
//        final ArrayOfQuantifiableVariable[] boundVars = 
//            new ArrayOfQuantifiableVariable[4];
//        boundVars[0] = new ArrayOfQuantifiableVariable (new QuantifiableVariable[] { var });
//        boundVars[1] = new ArrayOfQuantifiableVariable (new QuantifiableVariable[] { var2 });
//        boundVars[2] = boundVars[0];
//        boundVars[3] = new ArrayOfQuantifiableVariable ();
//            
//        final QuanUpdateOperator op =
//            QuanUpdateOperator.createUpdateOp( new Term[] { avar2 },
//                                               new boolean[] { false } );
//        final Term updTerm = tf.createQuanUpdateTerm(op, subTerms, boundVars);
//
//        assertEqualsModRenaming ( proof.simplifier ().simplify ( u1, 
//        							 nonRigidTarget,
//        							 services),
//                                  updTerm );
//    }
//    
//    public void testApplicationWithCollision() {
//	final Services services = proof.getServices();
//        final UpdateFactory fac = new UpdateFactory ( services, 
//                simplifier );
//
//        final Update u2 = fac.elementaryUpdate ( avar, bvar );
//        final Update u1 = fac.quantify ( var, u2 );
//
//        // otherwise we don't have a real collision ...
//        assertSame ( u1.getAssignmentPair ( 0 ).boundVars ().getQuantifiableVariable ( 0 ),
//                     var );
//        
//        assertEqualsModRenaming ( proof.simplifier ().simplify ( u1, avar, services ), bvar );
//        assertEqualsModRenaming ( proof.simplifier ().simplify ( u2, avar, services ), bvar );
//        
//        // try to substitute a free variable in a quantifier scope ...
//        final Term quantifierFor =
//            tf.createQuantifierTerm ( Op.ALL, var, tf.createEqualityTerm ( o, avar ) );
//        final Update u3 = fac.elementaryUpdate ( o, bvar );
//        
//        final Term resultFor =
//            tf.createQuantifierTerm ( Op.ALL, var2, tf.createEqualityTerm ( bvar, avar2 ) );
//        assertEqualsModRenaming ( proof.simplifier ().simplify ( u3, quantifierFor, services ),
//                                  resultFor );        
//    }
//    
//    public void testCollisionWhenAddingGuard() {
//	final Services services = proof.getServices();
//        final UpdateFactory fac = new UpdateFactory ( services, 
//                                                      simplifier );
//
//        final Update u1 = fac.guard ( tf.createEqualityTerm ( avar, bvar ),
//                                      fac.quantify ( var,
//                                                     fac.elementaryUpdate ( avar,
//                                                                            bvar ) ) );
//        final Update u2 = fac.guard ( tf.createEqualityTerm ( avar, bvar ),
//                                      fac.quantify ( var2,
//                                                     fac.elementaryUpdate ( avar2,
//                                                                            bvar2 ) ) );
//        assertEqualsModRenaming ( proof.simplifier ().simplify ( u1, 
//        							 nonRigidTarget, 
//        							 services ),
//                                  proof.simplifier ().simplify ( u2, 
//                                	  			 nonRigidTarget, 
//                                	  			 services ) );
//    }
//    
//    public void testEffectLess () {
//        // test that an earlier bug is no longer present:
//        // the update factory correctly creates effectless assignment
//        // updates a:=a, the different constructors provided by the factory
//        // do not eliminate such assignments
//        
//        final UpdateFactory fac = new UpdateFactory ( proof.getServices(), 
//                                                      simplifier );
//        
//        final Update effectFull = fac.elementaryUpdate ( o, u );
//        
//        final Update effectLess0 = fac.elementaryUpdate ( o, o );
//        final Update effectLess1 = fac.parallel ( effectLess0, effectLess0 );
//        final Update effectLess2 = fac.sequential ( effectLess0, effectLess0 );
//        final Update effectLess3 = fac.quantify ( var, effectLess0 );
//        final Update effectLess4 = fac.guard ( tf.createJunctorTerm ( Op.TRUE ),
//                                               effectLess0 );
//        final Update effectLess5 = fac.apply ( fac.skip(), effectLess0 );
//        
//        assertEquals ( o, fac.apply ( fac.parallel ( effectFull, effectLess0 ), o ) );
//        assertEquals ( o, fac.apply ( fac.parallel ( effectFull, effectLess1 ), o ) );
//        assertEquals ( o, fac.apply ( fac.parallel ( effectFull, effectLess2 ), o ) );
//        assertEquals ( o, fac.apply ( fac.parallel ( effectFull, effectLess3 ), o ) );
//        assertEquals ( o, fac.apply ( fac.parallel ( effectFull, effectLess4 ), o ) );
//        assertEquals ( o, fac.apply ( fac.parallel ( effectFull, effectLess5 ), o ) );
//    }
//
//    
//    private void clear(Proof proof, Namespace variables, 
//            Namespace functions, Namespace sorts, 
//            ProgramVariable[] pv, TermFactory tf, 
//            Sort testSort0, 
//            Sort testSort1, Sort testSort2, Sort cloneable, Sort serializable, Sort integerSort, Term t, Term i, Term o, Term u, Term oa, Term ua, Term phi, Term psi, ArraySort arraySort1, ArraySort arraySort2, Term a, 
//            Term b, NonRigidFunction nonRigidTargetOp, Term nonRigidTarget, QuantifiableVariable var, Term varT, QuantifiableVariable var2, Term var2T, Function f, Term fvarvar2, Term avar, Term bvar, 
//            Term avar2, Term avarvar2, Term bvar2, Function woRelation,
//            UpdateSimplifier simplifier) {
//        this.proof = proof;
//        this.variables = variables;
//        this.functions = functions;
//        this.sorts = sorts;
//        this.pv = pv;      
//        this.testSort0 = testSort0;
//        this.testSort1 = testSort1;
//        this.testSort2 = testSort2;
//        this.cloneable = cloneable;
//        this.serializable = serializable;
//        this.integerSort = integerSort;
//        this.t = t;
//        this.i = i;
//        this.o = o;
//        this.u = u;
//        this.oa = oa;
//        this.ua = ua;
//        this.phi = phi;
//        this.psi = psi;
//        this.arraySort1 = arraySort1;
//        this.arraySort2 = arraySort2;
//        this.a = a;
//        this.b = b;
//        this.nonRigidTargetOp = nonRigidTargetOp;
//        this.nonRigidTarget = nonRigidTarget;
//        this.var = var;
//        this.varT = varT;
//        this.var2 = var2;
//        this.var2T = var2T;
//        this.f = f;
//        this.fvarvar2 = fvarvar2;
//        this.avar = avar;
//        this.bvar = bvar;
//        this.avar2 = avar2;
//        this.avarvar2 = avarvar2;
//        this.bvar2 = bvar2;
//        this.woRelation = woRelation;
//        this.simplifier = simplifier;
//    }
}
