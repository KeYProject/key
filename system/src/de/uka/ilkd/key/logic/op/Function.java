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



package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Objects of this class represent function and predicate symbols. Note
 * that program variables are a separate syntactic category, and not a type
 * of function.
 */
public class Function extends AbstractSortedOperator {

    private final boolean unique;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------     

    Function(Name name,
             Sort sort,
             ImmutableArray<Sort> argSorts,
             ImmutableArray<Boolean> whereToBind,
             boolean unique,
             boolean isRigid) {
	super(name, argSorts, sort, whereToBind, isRigid);
	this.unique = unique;
	assert sort != Sort.UPDATE;
	assert !(unique && sort == Sort.FORMULA);
	assert !(sort instanceof NullSort) || name.toString().equals("null")
	       : "Functions with sort \"null\" are not allowed: " + this;
    }

    public Function(Name name,
                    Sort sort,
                    ImmutableArray<Sort> argSorts,
                    ImmutableArray<Boolean> whereToBind,
                    boolean unique) {
        this(name, sort, argSorts, whereToBind, unique, true);
    }

    public Function(Name name,
                    Sort sort,
                    Sort[] argSorts,
                    Boolean[] whereToBind,
                    boolean unique) {
	this(name,
             sort,
             new ImmutableArray<Sort>(argSorts),
             whereToBind == null ? null : new ImmutableArray<Boolean>(whereToBind),
             unique);
    }

    Function(Name name, Sort sort, ImmutableArray<Sort> argSorts, boolean isRigid) {
        this(name, sort, argSorts, null, false, isRigid);
    }

    public Function(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
	this(name, sort, argSorts, null, false);
    }

    public Function(Name name, Sort sort, Sort ... argSorts) {
	this(name, sort, argSorts, null, false);
    }

    public Function(Name name, Sort sort) {
	this(name, sort, new ImmutableArray<Sort>(), null, false);
    }


    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------     

    /**
     * Indicates whether the function or predicate symbol has the "uniqueness"
     * property. For two unique symbols f1: A1 -> B1, f2: A2 -> B2 by definition
     * we have
     * (1) f1(x) != f1(y) for all x, y in A1 with x != y (i.e., injectivity),
     * and (2) f1(x) != f2(y) for all x in A1, y in A2.
     */
    public final boolean isUnique() {
	return unique;
    }


    @Override
    public final String toString() {
	return (name() + (whereToBind() == null
		          ? ""
		          : "{" + whereToBind() + "}"));
    }

    /**
     * Returns a parsable string representation of the declaration of this
     * function or predicate symbol.
     */
    public final String proofToString() {
       String s =
	   (sort() == Sort.FORMULA ? "" : sort().toString()) + " ";
       s += name();
       if (arity()>0) {
          int i = 0;
          s+="(";
          while (i<arity()) {
             if (i>0) s+=",";
             s+=argSort(i);
             i++;
          }
          s+=")";
       }
       s+=";\n";
       return s;
    }
}