// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.encapsulation;


final class TypeSchemeUnion implements TypeSchemeTerm {
    public static final TypeSchemeUnion PRIMITIVE
            = new TypeSchemeUnion(PrimitiveScheme.INSTANCE);
    public static final TypeSchemeUnion NULL 
            = new TypeSchemeUnion(NullScheme.INSTANCE);
    public static final TypeSchemeUnion THIS
            = new TypeSchemeUnion(ThisScheme.INSTANCE);
    public static final TypeSchemeUnion REP 
            = new TypeSchemeUnion(RepScheme.INSTANCE);
    public static final TypeSchemeUnion PEER 
            = new TypeSchemeUnion(PeerScheme.INSTANCE);
    public static final TypeSchemeUnion READONLY 
            = new TypeSchemeUnion(ReadonlyScheme.INSTANCE);
    public static final TypeSchemeUnion READONLYPRIME 
            = new TypeSchemeUnion(ReadonlyPrimeScheme.INSTANCE);
    public static final TypeSchemeUnion ROOT 
            = new TypeSchemeUnion(RootScheme.INSTANCE);
    public static final TypeSchemeUnion READONLY_ROOT
            = new TypeSchemeUnion(new TypeScheme[] {ReadonlyScheme.INSTANCE,
                                                    RootScheme.INSTANCE});
    public static final TypeSchemeUnion REP_PEER_ROOT
            = new TypeSchemeUnion(new TypeScheme[] {RepScheme.INSTANCE,
                                                    PeerScheme.INSTANCE,
                                                    RootScheme.INSTANCE});
    public static final TypeSchemeUnion REP_PEER_READONLY_ROOT
    	    = new TypeSchemeUnion(new TypeScheme[] {RepScheme.INSTANCE,
                                                    PeerScheme.INSTANCE,
                                                    ReadonlyScheme.INSTANCE,
                                                    RootScheme.INSTANCE});
    public static final TypeSchemeUnion PRIMITIVE_REP_PEER_READONLY_ROOT
            = new TypeSchemeUnion(new TypeScheme[] {PrimitiveScheme.INSTANCE,
                                                    RepScheme.INSTANCE,
                                                    PeerScheme.INSTANCE,
                                                    ReadonlyScheme.INSTANCE,
                                                    RootScheme.INSTANCE});
    
    
    private SetOfTypeScheme possibilities;   
    
    
    public TypeSchemeUnion(TypeScheme ts) {
        possibilities = SetAsListOfTypeScheme.EMPTY_SET.add(ts);
    }
    
    
    public TypeSchemeUnion(SetOfTypeScheme possibilities) {
        this.possibilities = possibilities;
    }
    
    
    public TypeSchemeUnion(TypeScheme[] schemes) {
        possibilities = SetAsListOfTypeScheme.EMPTY_SET;
        for(int i = schemes.length - 1; i >= 0; i--) {
            possibilities = possibilities.add(schemes[i]);
        }
    }
    
    
    public SetOfTypeScheme getPossibilities() {
        return possibilities;
    }


    public boolean isExact() {
        return possibilities.size() == 1;
    }
    

    public TypeSchemeUnion combineWith(TypeSchemeUnion tsu) {
        SetOfTypeScheme resultPossibilities 
                = SetAsListOfTypeScheme.EMPTY_SET;

        IteratorOfTypeScheme it = possibilities.iterator();
        while(it.hasNext()) {
            TypeScheme myTs = it.next();

            IteratorOfTypeScheme it2 = tsu.possibilities.iterator();
            while(it2.hasNext()) {
                TypeScheme otherTs = it2.next();
                TypeScheme combinedTs = myTs.combineWith(otherTs);
                resultPossibilities = resultPossibilities.add(combinedTs);
            }
        }

        return new TypeSchemeUnion(resultPossibilities);
    }

    
    public boolean subSchemeOf(TypeSchemeUnion tsu) {
        IteratorOfTypeScheme it = possibilities.iterator();
        while(it.hasNext()) {
            TypeScheme myTs = it.next();

            IteratorOfTypeScheme it2 = tsu.possibilities.iterator();
            while(it2.hasNext()) {
                TypeScheme otherTs = it2.next();
                if(myTs.subSchemeOf(otherTs)) {
                    return true;
                }
            }
        }

        return false;
    }
    
    
    public boolean equalTo(TypeSchemeUnion tsu) {
        IteratorOfTypeScheme it = possibilities.iterator();
        while(it.hasNext()) {
            TypeScheme myTs = it.next();
            
            IteratorOfTypeScheme it2 = tsu.possibilities.iterator();
            while(it2.hasNext()) {
                TypeScheme otherTs = it2.next();
                if(myTs.equalTo(otherTs)) {
                    return true;
                }
            }
        }
        
        return false;
    }
    
    
    public TypeSchemeUnion evaluate() {
        return this;
    }
    
    
    public SetOfTypeSchemeVariable getFreeVars() {
        return SetAsListOfTypeSchemeVariable.EMPTY_SET;
    }
    
    
    public String toString() {
        String result = "[";
        IteratorOfTypeScheme it = possibilities.iterator();
        while(it.hasNext()) {
            result += it.next() + ",";
        }
        
        if(possibilities.size() > 0) {
            result = result.substring(0, result.length() - 1);
        }
        
        result += "]";
        
        return result;
    }
}
