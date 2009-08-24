// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;

/**
 * A Namespace keeps track of already used {@link Name}s and the objects
 * carrying these names. These objects have to implement the interface
 * {@link Named}. It is possible to have nested namespaces in order to
 * represent different visibility scopes. An instance of Namespace can
 * operate in normal and protocoled mode, where the protocoled mode
 * keeps track of all new added names since the last call of {@link
 * Namespace#startProtocol}.
 */
public class Namespace implements java.io.Serializable {

    /** 
     * The fall-back namespace for symbols not present in this
     * Namespace.
     */
    protected Namespace parent=null;    

    /** The hashmap that maps a name to a symbols of that name if it 
     * is defined in this Namespace. */
    protected HashMap<Name, Named> symbols=null;
     
    /** One defined symbol.  Many Namespaces, e.g. those generated when 
     * a quantified formula is parsed, define only one new symbol,
     * and it would be a waste of time and space to create a hashmap for that.
     * So {@link #symbols} is only initialized when there is more than one
     * symbol in this namespace.  Otherwise, <code>localSym</code> contains
     * that symbol. */
    protected Named localSym=null;

    /** The number of symbols defined in this namespace.  This is different 
     * from <code>symbols.size()</code> because symbols might be null if
     * there is only one symbol in this Namespace. */
    protected int numLocalSyms=0;

    /** Additions can be "recorded" here */
    protected HashMap<Name, Named> protocol = null;


    /** Construct an empty Namespace without a parent namespace. */
    public Namespace() {
	this.parent = null;
    }

    /** Construct an empty Namespace with protocol <code>protocol</code> 
     * and without a parent namespace. */
    public Namespace(HashMap<Name, Named> protocol) {
	this.parent = null;
	this.protocol = protocol;
    }

    /** Construct a Namespace that uses <code>parent</code> as a fallback
     * for finding symbols not defined in this one. */
    public Namespace(Namespace parent) {
	this.parent=parent;
    }

    /** Construct a Namespace that uses <code>parent</code> as a fallback
     * for finding symbols not defined in this one.  Put an entry for
     * <code>sym</code> in this one. */
    public Namespace(Namespace parent, Named sym) {
	this.parent=parent;
	add(sym);
    }

    /** Adds the object <code>sym</code> to this Namespace. 
     * If an object with the same name is already there, it is quietly 
     * replaced by <code>sym</code>. Use addSafely() instead if possible.
     * TODO:The problem of saving to localSym, symbols, and symbolRefs is not solved yet.*/
    public void add(Named sym) {
	if (numLocalSyms>0) {
                if (symbols == null) {
                    symbols = new HashMap<Name, Named>();
                    if (localSym != null) {
                        symbols.put(localSym.name(), localSym);
                        localSym = null;
                    }
                }
                symbols.put(sym.name(), sym);
            }
	else localSym=sym;
	numLocalSyms++;
        if (protocol != null) {
	    protocol.put(sym.name(),sym); 
        }
    }
    
    /** Adds the object <code>sym</code> to this namespace. 
     * Throws a runtime exception if an object with the same name is 
     * already there. */
    public void addSafely(Named sym) {
        if(lookup(sym.name()) != null) {
            throw new RuntimeException("Name already in namespace: " 
                                       + sym.name());
        }
        add(sym);
    }
    
    /** "remember" all additions from now on */
    public void startProtocol() {
        protocol = new HashMap<Name, Named>();
    }

    /** gets symbols added since last <code>startProtocol()</code>;
     *  resets the protocol */
    public Iterator<Named> getProtocolled() {
        if (protocol == null) {
            return ImmutableSLList.<Named>nil().iterator();
        }
        final Iterator<Named> it = protocol.values().iterator();
        protocol = null;
        return it;
    }
    

    protected Named lookupLocally(Name name){
	if (numLocalSyms==0) return null;
	if (numLocalSyms > 1) {
            if (symbols != null && symbols.containsKey(name)) {
                return symbols.get(name);
            } 
            return null;
        }
	if (localSym.name().equals(name)) {
	    return localSym;
	}
	else return null;
    }  


    /** creates a new Namespace that has this as parent, and contains
     * an entry for <code>sym</code>.
     * @return the new Namespace
     */
    public Namespace extended(Named sym) {
	return new Namespace(this, sym);
    }

    public Namespace extended(ImmutableList<Named> ext) {
	Namespace res=new Namespace(this);
	Iterator<Named> it=ext.iterator();
	while (it.hasNext()) {
	    res.add(it.next());
	}
	return res;
    }

   /** 
    * looks if a registered object is declared in this namespace, if
    * negative it asks its parent 
    * @param name a Name representing the name of the symbol to look for
    * @return Object with name "name" or null if no such an object
    * has been found
    */  
    public Named lookup(Name name) {
	Named symbol=lookupLocally(name);
	if (symbol==null && parent!=null) {
	    return parent.lookup(name);
	} else {
	    return symbol;
	}
    }
    
    /** returns list of the elements (not the keys) in this
     * namespace (not about the one of the parent)
     * @return the list of the named objects
     */
    public ImmutableList<Named> elements() {
	ImmutableList<Named> list = ImmutableSLList.<Named>nil();

	if (numLocalSyms == 1) {
            list = list.prepend(localSym);
        } else if (numLocalSyms > 1) {          
            if (symbols != null) {
                Iterator<Named> it = symbols.values().iterator();
                while (it.hasNext()) {
                    Named named = it.next();
                    if (named != null) {
                        list = list.prepend(named);
                    }
                }
            }
        }

	return list;
    }

    public ImmutableList<Named> allElements() {
	if (parent==null) {
	    return elements();
	} else {
	    return elements().append(parent().allElements());
	}
    }

    /** returns the fall-back Namespace of this Namespace, i.e. the one
     * where symbols are looked up that are not found in this one.
     */
    public Namespace parent() {
	return parent;
    }

    public String toString() {
	String res="Namespace: [local:"+localSym+", "+symbols;
	if (parent!=null) res=res+"; parent:"+parent;
	return res+"]";
    }

    public void add(Namespace source) {
	Iterator<Named> it=source.elements().iterator();
	while (it.hasNext()) {
	    add(it.next());
	}
	
    }

    public void add(ImmutableList<Named> l) {
	Iterator<Named> it = l.iterator();
	while (it.hasNext()) {
	    add(it.next());
	}
    }

    public Namespace copy() {
	Namespace copy;
	if(protocol != null){
	    copy = new Namespace((HashMap<Name, Named>)protocol.clone());
	}else{
	    copy = new Namespace();
	}
	//%%%%make more efficient!!!
	Iterator<Named> it=allElements().iterator();
	while (it.hasNext()) {
	    copy.add(it.next());
	}
	return copy;
    }
    
    public void reset() {
	parent=null;
	symbols=null;	
	localSym=null;
	numLocalSyms=0;
    }
}
