// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * Abstract superclass of all skolem builders
 */
public abstract class AbstractSkolemBuilder implements SkolemBuilder {

    private static int skolemCnt = 0;

    private final Services  services;

    private final SkolemSet oriSkolemSet;
    private SVInstantiations svi;

    public AbstractSkolemBuilder ( SkolemSet p_oriSkolemSet,
                                   Services  p_services ) {
	oriSkolemSet = p_oriSkolemSet;
	services     = p_services;
	setSVI(getOriginalSkolemSet ().getInstantiations ());
    }

    /**
     * The formula for which skolem symbols are to be created
     */
    protected Term getOriginalFormula () {
	return getOriginalSkolemSet ().getFormula ();
    }

    private void setSVI(SVInstantiations svi) {
        this.svi = svi;
    }

    protected SVInstantiations getSVI() {
        return svi;
    }

    /**
     * The object that is to be enriched by further skolem symbols
     */
    protected SkolemSet getOriginalSkolemSet () {
	return oriSkolemSet;
    }

    protected IteratorOfSkolemSet toIterator ( SkolemSet p ) {
	return SLListOfSkolemSet.EMPTY_LIST.prepend ( p ).iterator ();
    }

    protected KeYJavaType getObjectKeYJavaType () {
	return getJavaInfo ().getJavaLangObject ();
    }

    /**
     * Add an instantiation to the SVInstantiations object
     */
    protected void addInstantiation ( SchemaVariable p_sv,
				      Term           p_term ) {
	setSVI(getSVI().add ( p_sv, p_term ));
    }

    /**
     * Add an instantiation to the SVInstantiations object
     */
    protected void addInstantiation ( SchemaVariable p_sv,
				      ProgramElement p_pe ) {
	setSVI(getSVI().add ( p_sv, p_pe ));
    }

    /**
     * Add an instantiation to the SVInstantiations object
     */
    protected void addInstantiation ( SchemaVariable p_sv,
				      ProgramElement p_pe,
				      int            p_instantiationType ) {
	setSVI(getSVI().add ( p_sv, p_pe, p_instantiationType ));
    }

    protected boolean isInstantiated(SchemaVariable p_sv) {
        return getSVI().isInstantiated ( p_sv );
    }

    protected SVPartitioning getSVPartitioning() {
        return getOriginalSkolemSet ().getSVPartitioning ();
    }

    protected KeYJavaType getPartitionType(int p_variableNumber) {
        return getSVPartitioning ().getType
            ( p_variableNumber, getOriginalSkolemSet().getSVTypeInfos() );
    }

    /**
     * Types that should be considered for untyped schema
     * variables. Currently only primitive types and the object type
     * are returned
     */
    protected IteratorOfKeYJavaType createTypeCandidates () {
	final Type[] primitiveTypes = new Type[] {
	    PrimitiveType.JAVA_BYTE,
	    PrimitiveType.JAVA_SHORT,
	    PrimitiveType.JAVA_INT,
	    PrimitiveType.JAVA_CHAR,
	    PrimitiveType.JAVA_LONG,
	    //	    PrimitiveType.JAVA_FLOAT,
	    //	    PrimitiveType.JAVA_DOUBLE,
	    PrimitiveType.JAVA_BOOLEAN,
	    //	    NullType.JAVA_NULL
	};
	
	ListOfKeYJavaType list = SLListOfKeYJavaType.EMPTY_LIST;
	int               i;

	for ( i = 0; i != primitiveTypes.length; ++i )
	    list = list.prepend ( getJavaInfo ()
				  .getKeYJavaType ( primitiveTypes[i] ) );

	list = list.prepend ( getObjectKeYJavaType ( ) );

	return list.iterator ();
    }

    protected Services getServices() {
        return services;
    }

    protected JavaInfo getJavaInfo() {
        return getServices ().getJavaInfo ();
    }


    /**
     * HACK: Create a new and unique identifier
     */
    static Name createUniqueName(String baseName) {
        return new Name ( baseName + "_" + skolemCnt++ );
    }

    /**
     * HACK: Create a new and unique identifier
     */
    static Name createUniqueName(Name baseName) {
        return createUniqueName("" + baseName);
    }

    /**
     * HACK: Create a new and unique identifier
     */
    static ProgramElementName createUniquePEName(String baseName) {
        return new ProgramElementName ( baseName + "_" + skolemCnt++ );
    }

    /**
     * HACK: Create a new and unique identifier
     */
    static ProgramElementName createUniquePEName(Name baseName) {
        return createUniquePEName("" + baseName);
    }

    protected TermFactory getTF() {
        return TermFactory.DEFAULT;
    }

}
