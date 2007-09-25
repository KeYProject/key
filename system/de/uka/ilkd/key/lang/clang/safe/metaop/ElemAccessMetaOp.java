package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.sort.object.IArraySort;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ElemFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.SizedArraySort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.UnsizedArraySort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that applies function <code>T::{elem}</code> to its
 * first argument of CDL array sort T and takes the element index from its
 * second argument.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ElemAccessMetaOp extends SafeBaseMetaOp {

        public ElemAccessMetaOp() {
                super(new Name("#ClangElemAccess"), 2);
        }

        /**
         * @inheritDocs
         */
        public Term calculate(Term term, IClangSafeEnvironment context) {
                Term term0 = term.sub(0);
                Term term1 = term.sub(1);
                
                UnsizedArraySort arraySort;
                if (term0.sort() instanceof UnsizedArraySort)
                        arraySort = (UnsizedArraySort)term0.sort();
                else if (term0.sort() instanceof IArraySort)
                        arraySort = ((SizedArraySort)term0.sort()).getUnsizedArraySort();
                else
                        throw new RuntimeException(
                                        "#ClangElemAccess applied to a term of non-array sort (array marker sort is not supported)");
                ElemFunction elemFunction = arraySort.getElemFunction();
                if (elemFunction.argSort(1) != term1.sort())
                        throw new RuntimeException(
                                        "#ClangElemAccess applied to the second argument that is not of int type");

                return TermFactory.DEFAULT.createFunctionTerm(elemFunction,
                                new Term[]{term0, term1});
        }
}
