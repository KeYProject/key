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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.logic.op.SchemaVariable;


/** this class wrapps a ImmMap<SchemaVariable,JavaProgramElement> and
 * is used to store instantiations of schemavariables. The class is
 * immutable, this means changing its content will result in creating
 * a new object. 
 */
public class ProgramSVInstantiation {

    /** the empty instantiation */
    public static final ProgramSVInstantiation 
	EMPTY_PROGRAMSVINSTANTIATION = new ProgramSVInstantiation();

    /** the map with the instantiations */
    private ImmutableList<ProgramSVEntry> list = ImmutableSLList.<ProgramSVEntry>nil();
    
    /** integer to cache the hashcode */
    private int hashcode = 0;
    

    /** creates a new ProgramSVInstantiation object with an empty list */
    private ProgramSVInstantiation() {
    }
    
    /** creates a new ProgramSVInstantiation object using the given list 
     * @param list the ListFromSchemaVariableToJavaProgramElement with the
     * instantiations
     */
    private ProgramSVInstantiation(ImmutableList<ProgramSVEntry> list) {
	this.list = list;
    }

    /** adds the given pair to the instantiations. If the given
     * SchemaVariable has been instantiated already, the new pair is
     * taken without a warning.
     * @param sv the SchemaVariable to be instantiated
     * @param prgElement the JavaProgramElement The SchemaVariable is
     * instantiated with 
     * @return ProgramSVInstantiation the new ProgramSVInstantiation
     * containing the given pair
     */
    public ProgramSVInstantiation add(SchemaVariable sv, 
				      JavaProgramElement prgElement) {
	if (!isInstantiated(sv)) {
	    return new ProgramSVInstantiation
		(list.prepend(new ProgramSVEntry(sv, prgElement)));
	} else {
	    return replace(sv, prgElement);
	}
    }    

    /** replaces the given pair in the instantiations. If the given
     * SchemaVariable has been instantiated already, the new pair is
     * taken without a warning.
     * @param sv the SchemaVariable to be instantiated
     * @param prgElement the JavaProgramElement The SchemaVariable is
     * instantiated with 
     * @return ProgramSVInstantiation the new ProgramSVInstantiation
     * containing the given pair
     */
    public ProgramSVInstantiation replace(SchemaVariable sv, 
					  JavaProgramElement prgElement) { 
	ImmutableList<ProgramSVEntry> result = ImmutableSLList.<ProgramSVEntry>nil()
	    .prepend(new ProgramSVEntry(sv, prgElement));
        for (final ProgramSVEntry entry : list) {
            if (entry.key() != sv) {
                result = result.prepend(entry);
            }
        }
	return new ProgramSVInstantiation(result);
    }    

    /** returns true iff the sv has been instantiated already 
     * @return true iff the sv has been instantiated already 
     */
    public boolean isInstantiated(SchemaVariable sv) {
        for (ProgramSVEntry entry : list) {
            if (entry.key() == sv) {
                return true;
            }
        }
	return false;
    }

    /** returns the instantiation of the given SchemaVariable
     * @return the JavaProgramElement the SchemaVariable will be
     * instantiated with, null if no instantiation is stored
     */
    public JavaProgramElement getInstantiation(SchemaVariable sv) {
        for (ProgramSVEntry entry : list) {
            if (entry.key() == sv) {
                return entry.value();
            }
        }
	return null;
    }


    /** returns iterator of the listped pair (SchemaVariables,
     * JavaProgramElement) 
     * @return the
     * Iterator<IEntry<SchemaVariable,JavaProgramElement>> 
     */
    public Iterator<ProgramSVEntry> iterator() {
	return list.iterator();
    }

    /** returns the number of SchemaVariables of which an
     * instantiation is known
     * @return int that is the number of SchemaVariables of which an
     * instantiation is known
     */
    public int size() {
	return list.size();
    }

    /** returns true if the given object and this one have the same
     * listpings
     * @return true if the given object and this one have the same
     * listpings
     */ 
    public boolean equals(Object obj) {
	ProgramSVInstantiation cmp;
	if (!(obj instanceof ProgramSVInstantiation)) {
	    return false;
	} else {
	    cmp = (ProgramSVInstantiation) obj;
	}
	if (size() != cmp.size()) {
	    return false;
	} else {
	    final Iterator<ProgramSVEntry> it = iterator();
	    while (it.hasNext()) {
                final ProgramSVEntry psv = it.next();
		if (!psv.value().equals
		    (cmp.getInstantiation(psv.key()))) {
		    return false;
		}
	    }
	    return true;
	}
    }
    
    public int hashCode(){
        if (hashcode == 0){
            int result = 17;
            final Iterator<ProgramSVEntry> it = iterator();
            while (it.hasNext()) {
                final ProgramSVEntry psv = it.next();
                result = 37 * result + psv.key().hashCode() + 
                    psv.value().hashCode();
            }
            hashcode = result;
        } 
        return hashcode;
    }

    /** toString */
    public String toString() {
	StringBuffer result = new StringBuffer("ProgramSVInstantiation:\n");
	return (result.append(list.toString())).toString();
    }
}
