// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on 15.04.2005
 */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.ExactInstanceSymbol;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/**
 * This meta constructs expands an object to all possible dynamic types. It
 * returns <code>true</code> if no dynamic types are possible
 * <em>Attention</em> strong closed world assumption
 */
public class ExpandDynamicType extends AbstractMetaOperator {

    /**
     * creates this meta construct
     */
    public ExpandDynamicType() {
        super(new Name("#expandDynamicType"), 1);
    }

    /**
     * determines the sort of the {@link Term}if it would be created using this
     * Operator as top level operator and the given terms as sub terms. The
     * assumption that the constructed term would be allowed is not checked.
     * 
     * @param term
     *            an array of Term containing the subterms of a (potential) term
     *            with this operator as top level operator
     * @return sort of the term with this operator as top level operator of the
     *         given substerms
     */
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }

    
    /**
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.logic.op.MetaOperator#calculate(de.uka.ilkd.key.logic.Term,
     *      de.uka.ilkd.key.rule.inst.SVInstantiations,
     *      de.uka.ilkd.key.java.Services)
     */
    public Term calculate(Term metaTerm, SVInstantiations svInst,
            Services services) {
        final TermBuilder df = TermBuilder.DF;
        final Term trueFml = df.tt();
        final Term term = metaTerm.sub(0);

        final JavaInfo ji = services.getJavaInfo();
        
        if (!(term.sort() instanceof ObjectSort)
                || term.sort() == Sort.NULL
                || ji.isAJavaCommonSort(term.sort())) {
            // the latter two cases cannot be expanded as their are 
            // potential infinity dynamic types (array "subclass" object and 
            // cloneable)            
            return trueFml;
        }

        // TODO: expand to array types
        ImmutableList<KeYJavaType> instantiableSubTypes;

        if (term.sort() instanceof ArraySort) {
            final ArraySort arraySort = ((ArraySort) term.sort());
            Sort componentSort = arraySort;
            int dimension = 0;
            do {
                componentSort = ((ArraySort) componentSort).elementSort();
                dimension++;
            } while (componentSort instanceof ArraySort);

            if (ji.isAJavaCommonSort(componentSort)) {
                // object has infinite many subtypes
                return trueFml;
            } else if (componentSort == services.getTypeConverter()
                    .getIntegerLDT().targetSort()) {
                // TODO: no idea how to handle this byte, short, int issue
                // but usually the other rules should be strong enough
                // How to determine if int[], byte[], short[] or long[]
                // is required?
                return trueFml;
            }

            instantiableSubTypes = getInstantiableArraySubTypes(services,
                    componentSort, dimension);
        } else {
            final KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(
                    term.sort());
            if (kjt == null) {
                return trueFml;
            }
            final ImmutableList<KeYJavaType> allSubtypes = services.getJavaInfo()
                    .getAllSubtypes(kjt).prepend(kjt);           
            instantiableSubTypes = getInstantiableTypes(allSubtypes);
        }

        final Iterator<KeYJavaType> it = instantiableSubTypes.iterator();
        final Term trueTerm = df.TRUE(services);

        Term result = df.equals(term, df.NULL(services));

        while (it.hasNext()) {
            final SortDefiningSymbols sort = (SortDefiningSymbols) it.next()
                    .getSort();
            final Function dynamicType = 
                (Function) sort.lookupSymbol(ExactInstanceSymbol.NAME);           
            Debug.assertTrue(dynamicType != null,
                    "instanceof not declared for ", sort);
            result = df.or(result, 
                           df.equals(TermFactory.DEFAULT.createFunctionTerm(dynamicType, term), 
                                    trueTerm));
        }

        return result;
    }

    /**
     * ensures the existance and returns all arrays assignment compatible to an
     * array with the given component sort and dimension
     */
    private ImmutableList<KeYJavaType> getInstantiableArraySubTypes(Services services,
            Sort componentSort, int dimension) {
        ImmutableList<KeYJavaType> instantiableSubTypes = ImmutableSLList.<KeYJavaType>nil();
        final KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(
                componentSort);

        ImmutableList<KeYJavaType> componentSubtypes = ImmutableSLList.<KeYJavaType>nil();
        if (componentSort instanceof ObjectSort) {
            componentSubtypes = services.getJavaInfo().getAllSubtypes(kjt);
        }
        componentSubtypes = componentSubtypes.prepend(kjt);

        final String[] typeNames = ensureArrayTypes(services, dimension,
                componentSubtypes);

        for (String typeName : typeNames) {
            KeYJavaType instType = services.getJavaInfo().getTypeByName(
                    typeName);
            Debug.assertTrue(instType != null);
            instantiableSubTypes = instantiableSubTypes.prepend(instType);
        }
        return instantiableSubTypes;
    }

    /**
     * ensures existance of array types with the given dimension and one of the
     * component types in <tt>componentSubtypes</code>
     */
    private String[] ensureArrayTypes(Services services, int dimension,
            ImmutableList<KeYJavaType> componentSubtypes) {
        String dim = "";
        for (int i = 0; i < dimension; i++) {
            dim += "[]";
        }
        Iterator<KeYJavaType> it = componentSubtypes.iterator();
        int count = 0;
        String[] typeNames = new String[componentSubtypes.size()];        

        StringBuffer decl = new StringBuffer("{");
        while (it.hasNext()) {
            typeNames[count] = it.next().getFullName() + dim;
            decl.append(typeNames[count]);
            decl.append(" u");
            decl.append(count);
            decl.append(";");
            count++;
        }
        decl.append("}");
        // ensures presence of array types
        services.getJavaInfo().readJavaBlock(decl.toString());
        return typeNames;
    }

    /**
     * returns all types which can be instantiated
     * 
     * @param allSubtypes
     *            the IList<KeYJavaTypes> to be looked through
     * @return all instantiable types
     */
    private ImmutableList<KeYJavaType> getInstantiableTypes(ImmutableList<KeYJavaType> allSubtypes) {
        ImmutableList<KeYJavaType> result = ImmutableSLList.<KeYJavaType>nil();
        for (KeYJavaType allSubtype : allSubtypes) {
            final KeYJavaType kjt = allSubtype;
            Type t = kjt.getJavaType();
            if (t instanceof ArrayType) {
                result = result.prepend(kjt);
            } else if (t instanceof ClassType &&
                    !((ClassType) t).isAbstract() &&
                    !((ClassType) t).isInterface()) {
                result = result.prepend(kjt);
            }
        }
        return result;
    }

}


